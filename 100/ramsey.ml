(* ======================================================================== *)
(* Infinite Ramsey's theorem.                                               *)
(*                                                                          *)
(* Port to HOL Light of a HOL88 proof done on 9th May 1994                  *)
(* ======================================================================== *)

(* ------------------------------------------------------------------------- *)
(* HOL88 compatibility.                                                      *)
(* ------------------------------------------------------------------------- *)

let is_neg_imp tm =
  is_neg tm or is_imp tm;;

let dest_neg_imp tm =
  try dest_imp tm with Failure _ ->
  try (dest_neg tm,mk_const("F",[]))
  with Failure _ -> failwith "dest_neg_imp";;

(* ------------------------------------------------------------------------- *)
(* These get overwritten by the subgoal stuff.                               *)
(* ------------------------------------------------------------------------- *)

let PROVE = prove;;

let prove_thm((s:string),g,t) = prove(g,t);;

(* ------------------------------------------------------------------------- *)
(* The quantifier movement conversions.                                      *)
(* ------------------------------------------------------------------------- *)

let (CONV_OF_RCONV: conv -> conv) =
  let rec get_bv tm =
    if is_abs tm then bndvar tm
    else if is_comb tm then try get_bv (rand tm) with Failure _ -> get_bv (rator tm)
    else failwith "" in
  fun conv tm ->
  let v = get_bv tm in
  let th1 = conv tm in
  let th2 = ONCE_DEPTH_CONV (GEN_ALPHA_CONV v) (rhs(concl th1)) in
  TRANS th1 th2;;

let (CONV_OF_THM: thm -> conv) =
  CONV_OF_RCONV o REWR_CONV;;

let (X_FUN_EQ_CONV:term->conv) =
  fun v -> (REWR_CONV FUN_EQ_THM) THENC GEN_ALPHA_CONV v;;

let (FUN_EQ_CONV:conv) =
  fun tm ->
    let vars = frees tm in
    let op,[ty1;ty2] = dest_type(type_of (lhs tm)) in
    if op = "fun"
       then let varnm =
                if (is_vartype ty1) then "x" else
                   hd(explode(fst(dest_type ty1))) in
            let x = variant vars (mk_var(varnm,ty1)) in
            X_FUN_EQ_CONV x tm
       else failwith "FUN_EQ_CONV";;

let (SINGLE_DEPTH_CONV:conv->conv) =
  let rec SINGLE_DEPTH_CONV conv tm =
    try conv tm with Failure _ ->
    (SUB_CONV (SINGLE_DEPTH_CONV conv) THENC (TRY_CONV conv)) tm in
  SINGLE_DEPTH_CONV;;

let (SKOLEM_CONV:conv) =
  SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM);;

let (X_SKOLEM_CONV:term->conv) =
  fun v -> SKOLEM_CONV THENC GEN_ALPHA_CONV v;;

let EXISTS_UNIQUE_CONV tm =
  let v = bndvar(rand tm) in
  let th1 = REWR_CONV EXISTS_UNIQUE_THM tm in
  let tm1 = rhs(concl th1) in
  let vars = frees tm1 in
  let v = variant vars v in
  let v' = variant (v::vars) v in
  let th2 =
   (LAND_CONV(GEN_ALPHA_CONV v) THENC
    RAND_CONV(BINDER_CONV(GEN_ALPHA_CONV v') THENC
              GEN_ALPHA_CONV v)) tm1 in
  TRANS th1 th2;;

let NOT_FORALL_CONV = CONV_OF_THM NOT_FORALL_THM;;

let NOT_EXISTS_CONV = CONV_OF_THM NOT_EXISTS_THM;;

let RIGHT_IMP_EXISTS_CONV = CONV_OF_THM RIGHT_IMP_EXISTS_THM;;

let FORALL_IMP_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
   REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
   REWR_CONV LEFT_FORALL_IMP_THM);;

let EXISTS_AND_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
   REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
   REWR_CONV RIGHT_EXISTS_AND_THM);;

let LEFT_IMP_EXISTS_CONV = CONV_OF_THM LEFT_IMP_EXISTS_THM;;

let LEFT_AND_EXISTS_CONV tm =
  let v = bndvar(rand(rand(rator tm))) in
  (REWR_CONV LEFT_AND_EXISTS_THM THENC TRY_CONV (GEN_ALPHA_CONV v)) tm;;

let RIGHT_AND_EXISTS_CONV =
  CONV_OF_THM RIGHT_AND_EXISTS_THM;;

let AND_FORALL_CONV = CONV_OF_THM AND_FORALL_THM;;

(* ------------------------------------------------------------------------- *)
(* The slew of named tautologies.                                            *)
(* ------------------------------------------------------------------------- *)

let AND1_THM = TAUT `!t1 t2. t1 /\ t2 ==> t1`;;

let AND2_THM = TAUT `!t1 t2. t1 /\ t2 ==> t2`;;

let AND_IMP_INTRO = TAUT `!t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3`;;

let AND_INTRO_THM = TAUT `!t1 t2. t1 ==> t2 ==> t1 /\ t2`;;

let BOOL_EQ_DISTINCT = TAUT `~(T <=> F) /\ ~(F <=> T)`;;

let EQ_EXPAND = TAUT `!t1 t2. (t1 <=> t2) <=> t1 /\ t2 \/ ~t1 /\ ~t2`;;

let EQ_IMP_THM = TAUT `!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)`;;

let FALSITY = TAUT `!t. F ==> t`;;

let F_IMP = TAUT `!t. ~t ==> t ==> F`;;

let IMP_DISJ_THM = TAUT `!t1 t2. t1 ==> t2 <=> ~t1 \/ t2`;;

let IMP_F = TAUT `!t. (t ==> F) ==> ~t`;;

let IMP_F_EQ_F = TAUT `!t. t ==> F <=> (t <=> F)`;;

let LEFT_AND_OVER_OR = TAUT
  `!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3`;;

let LEFT_OR_OVER_AND = TAUT
  `!t1 t2 t3. t1 \/ t2 /\ t3 <=> (t1 \/ t2) /\ (t1 \/ t3)`;;

let NOT_AND = TAUT `~(t /\ ~t)`;;

let NOT_F = TAUT `!t. ~t ==> (t <=> F)`;;

let OR_ELIM_THM = TAUT
  `!t t1 t2. t1 \/ t2 ==> (t1 ==> t) ==> (t2 ==> t) ==> t`;;

let OR_IMP_THM = TAUT `!t1 t2. (t1 <=> t2 \/ t1) <=> t2 ==> t1`;;

let OR_INTRO_THM1 = TAUT `!t1 t2. t1 ==> t1 \/ t2`;;

let OR_INTRO_THM2 = TAUT `!t1 t2. t2 ==> t1 \/ t2`;;

let RIGHT_AND_OVER_OR = TAUT
  `!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1`;;

let RIGHT_OR_OVER_AND = TAUT
  `!t1 t2 t3. t2 /\ t3 \/ t1 <=> (t2 \/ t1) /\ (t3 \/ t1)`;;

(* ------------------------------------------------------------------------- *)
(* This is an overwrite -- is there any point in what I have?                *)
(* ------------------------------------------------------------------------- *)

let is_type = can get_type_arity;;

(* ------------------------------------------------------------------------- *)
(* I suppose this is also useful.                                            *)
(* ------------------------------------------------------------------------- *)

let is_constant = can get_const_type;;

(* ------------------------------------------------------------------------- *)
(* Misc.                                                                     *)
(* ------------------------------------------------------------------------- *)

let null l = l = [];;

(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

let type_tyvars = type_vars_in_term o curry mk_var "x";;

let find_match u =
  let rec find_mt t =
    try term_match [] u t with Failure _ ->
    try find_mt(rator t) with Failure _ ->
    try find_mt(rand  t) with Failure _ ->
    try find_mt(snd(dest_abs t))
    with Failure _ -> failwith "find_match" in
  fun t -> let _,tmin,tyin = find_mt t in
           tmin,tyin;;

let rec mk_primed_var(name,ty) =
  if can get_const_type name then mk_primed_var(name^"'",ty)
  else mk_var(name,ty);;

let subst_occs =
  let rec subst_occs slist tm =
    let applic,noway = partition (fun (i,(t,x)) -> aconv tm x) slist in
    let sposs = map (fun (l,z) -> let l1,l2 = partition ((=) 1) l in
                                  (l1,z),(l2,z)) applic in
    let racts,rrest = unzip sposs in
    let acts = filter (fun t -> not (fst t = [])) racts in
    let trest = map (fun (n,t) -> (map (C (-) 1) n,t)) rrest in
    let urest = filter (fun t -> not (fst t = [])) trest in
    let tlist = urest @ noway in
      if acts = [] then
      if is_comb tm then
        let l,r = dest_comb tm in
        let l',s' = subst_occs tlist l in
        let r',s'' = subst_occs s' r in
        mk_comb(l',r'),s''
      else if is_abs tm then
        let bv,bod = dest_abs tm in
        let gv = genvar(type_of bv) in
        let nbod = vsubst[gv,bv] bod in
        let tm',s' = subst_occs tlist nbod in
        alpha bv (mk_abs(gv,tm')),s'
      else
        tm,tlist
    else
      let tm' = (fun (n,(t,x)) -> subst[t,x] tm) (hd acts) in
      tm',tlist in
  fun ilist slist tm -> fst(subst_occs (zip ilist slist) tm);;

(* ------------------------------------------------------------------------- *)
(* Note that the all-instantiating INST and INST_TYPE are not overwritten.   *)
(* ------------------------------------------------------------------------- *)

let INST_TY_TERM(substl,insttyl) th =
  let th' = INST substl (INST_TYPE insttyl th) in
  if hyp th' = hyp th then th'
  else failwith "INST_TY_TERM: Free term and/or type variables in hypotheses";;

(* ------------------------------------------------------------------------- *)
(* Conversions stuff.                                                        *)
(* ------------------------------------------------------------------------- *)

let RIGHT_CONV_RULE (conv:conv) th =
  TRANS th (conv(rhs(concl th)));;

(* ------------------------------------------------------------------------- *)
(* Derived rules.                                                            *)
(* ------------------------------------------------------------------------- *)

let NOT_EQ_SYM =
  let pth = GENL [`a:A`; `b:A`]
    (GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM] (DISCH_ALL(SYM(ASSUME`a:A = b`))))
  and aty = `:A` in
  fun th -> try let l,r = dest_eq(dest_neg(concl th)) in
                MP (SPECL [r; l] (INST_TYPE [type_of l,aty] pth)) th
            with Failure _ -> failwith "NOT_EQ_SYM";;

let NOT_MP thi th =
  try MP thi th with Failure _ ->
  try let t = dest_neg (concl thi) in
      MP(MP (SPEC t F_IMP) thi) th
  with Failure _ -> failwith "NOT_MP";;

let FORALL_EQ x =
  let mkall = AP_TERM (mk_const("!",[type_of x,mk_vartype "A"])) in
  fun th -> try mkall (ABS x th)
            with Failure _ -> failwith "FORALL_EQ";;

let EXISTS_EQ x =
  let mkex = AP_TERM (mk_const("?",[type_of x,mk_vartype "A"])) in
  fun th -> try mkex (ABS x th)
            with Failure _ -> failwith "EXISTS_EQ";;

let SELECT_EQ x =
  let mksel = AP_TERM (mk_const("@",[type_of x,mk_vartype "A"])) in
  fun th -> try mksel (ABS x th)
            with Failure _ -> failwith "SELECT_EQ";;

let RIGHT_BETA th =
  try TRANS th (BETA_CONV(rhs(concl th)))
  with Failure _ -> failwith "RIGHT_BETA";;

let rec LIST_BETA_CONV tm =
  try let rat,rnd = dest_comb tm in
      RIGHT_BETA(AP_THM(LIST_BETA_CONV rat)rnd)
  with Failure _ -> REFL tm;;

let RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(snd(dest_eq(concl th))));;

let LIST_CONJ = end_itlist CONJ ;;

let rec CONJ_LIST n th =
  try if n=1 then [th] else (CONJUNCT1 th)::(CONJ_LIST (n-1) (CONJUNCT2 th))
  with Failure _ -> failwith "CONJ_LIST";;

let rec BODY_CONJUNCTS th =
  if is_forall(concl th) then
    BODY_CONJUNCTS (SPEC_ALL th) else
  if is_conj (concl th) then
      BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th)
  else [th];;

let rec IMP_CANON th =
    let w = concl th in
    if is_conj w then IMP_CANON (CONJUNCT1 th) @ IMP_CANON (CONJUNCT2 th)
    else if is_imp w then
        let ante,conc = dest_neg_imp w in
        if is_conj ante then
            let a,b = dest_conj ante in
            IMP_CANON
            (DISCH a (DISCH b (NOT_MP th (CONJ (ASSUME a) (ASSUME b)))))
        else if is_disj ante then
            let a,b = dest_disj ante in
            IMP_CANON (DISCH a (NOT_MP th (DISJ1 (ASSUME a) b))) @
            IMP_CANON (DISCH b (NOT_MP th (DISJ2 a (ASSUME b))))
        else if is_exists ante then
            let x,body = dest_exists ante in
            let x' = variant (thm_frees th) x in
            let body' = subst [x',x] body in
            IMP_CANON
            (DISCH body' (NOT_MP th (EXISTS (ante, x') (ASSUME body'))))
        else
        map (DISCH ante) (IMP_CANON (UNDISCH th))
    else if is_forall w then
        IMP_CANON (SPEC_ALL th)
    else [th];;

let LIST_MP  = rev_itlist (fun x y -> MP y x);;

let DISJ_IMP =
  let pth = TAUT`!t1 t2. t1 \/ t2 ==> ~t1 ==> t2` in
  fun th ->
    try let a,b = dest_disj(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "DISJ_IMP";;

let IMP_ELIM =
  let pth = TAUT`!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2` in
  fun th ->
    try let a,b = dest_imp(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "IMP_ELIM";;

let DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);;

let MK_ABS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = SPEC_VAR qth in
      let sth = ABS bv rth in
      let cnv = ALPHA_CONV ov in
      CONV_RULE(BINOP_CONV cnv) sth
  with Failure _ -> failwith "MK_ABS";;

let HALF_MK_ABS th =
  try let th1 = MK_ABS th in
      CONV_RULE(LAND_CONV ETA_CONV) th1
  with Failure _ -> failwith "HALF_MK_ABS";;

let MK_EXISTS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = SPEC_VAR qth in
      let sth = EXISTS_EQ bv rth in
      let cnv = GEN_ALPHA_CONV ov in
      CONV_RULE(BINOP_CONV cnv) sth
  with Failure _ -> failwith "MK_EXISTS";;

let LIST_MK_EXISTS l th = itlist (fun x th -> MK_EXISTS(GEN x th)) l th;;

let IMP_CONJ th1 th2 =
  let A1,C1 = dest_imp (concl th1) and A2,C2 = dest_imp (concl th2) in
  let a1,a2 = CONJ_PAIR (ASSUME (mk_conj(A1,A2))) in
      DISCH (mk_conj(A1,A2)) (CONJ (MP th1 a1) (MP th2 a2));;

let EXISTS_IMP x =
  if not (is_var x) then failwith "EXISTS_IMP: first argument not a variable"
  else fun th ->
         try let ante,cncl = dest_imp(concl th) in
             let th1 = EXISTS (mk_exists(x,cncl),x) (UNDISCH th) in
             let asm = mk_exists(x,ante) in
             DISCH asm (CHOOSE (x,ASSUME asm) th1)
         with Failure _ -> failwith "EXISTS_IMP: variable free in assumptions";;


let CONJUNCTS_CONV (t1,t2) =
  let rec build_conj thl t =
    try let l,r = dest_conj t in
        CONJ (build_conj thl l) (build_conj thl r)
    with Failure _ -> find (fun th -> concl th = t) thl in
  try IMP_ANTISYM_RULE
     (DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2))
     (DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1))
  with Failure _ -> failwith "CONJUNCTS_CONV";;

let CONJ_SET_CONV l1 l2 =
  try CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)
  with Failure _ -> failwith "CONJ_SET_CONV";;

let FRONT_CONJ_CONV tml t =
 let rec remove x l =
    if hd l = x then tl l else (hd l)::(remove x (tl l)) in
 try CONJ_SET_CONV tml (t::(remove t tml))
 with Failure _ -> failwith "FRONT_CONJ_CONV";;

let CONJ_DISCH =
  let pth = TAUT`!t t1 t2. (t ==> (t1 <=> t2)) ==> (t /\ t1 <=> t /\ t2)` in
  fun t th ->
    try let t1,t2 = dest_eq(concl th) in
        MP (SPECL [t; t1; t2] pth) (DISCH t th)
    with Failure _ -> failwith "CONJ_DISCH";;

let rec CONJ_DISCHL l th =
  if l = [] then th else CONJ_DISCH (hd l) (CONJ_DISCHL (tl l) th);;

let rec GSPEC th =
  let wl,w = dest_thm th in
  if is_forall w then
      GSPEC (SPEC (genvar (type_of (fst (dest_forall w)))) th)
  else th;;

let ANTE_CONJ_CONV tm =
  try let (a1,a2),c = (dest_conj F_F I) (dest_imp tm) in
      let imp1 = MP (ASSUME tm) (CONJ (ASSUME a1) (ASSUME a2)) and
          imp2 = LIST_MP [CONJUNCT1 (ASSUME (mk_conj(a1,a2)));
                          CONJUNCT2 (ASSUME (mk_conj(a1,a2)))]
                         (ASSUME (mk_imp(a1,mk_imp(a2,c)))) in
      IMP_ANTISYM_RULE (DISCH_ALL (DISCH a1 (DISCH a2 imp1)))
                       (DISCH_ALL (DISCH (mk_conj(a1,a2)) imp2))
  with Failure _ -> failwith "ANTE_CONJ_CONV";;

let bool_EQ_CONV =
  let check = let boolty = `:bool` in check (fun tm -> type_of tm = boolty) in
  let clist = map (GEN `b:bool`)
                  (CONJUNCTS(SPEC `b:bool` EQ_CLAUSES)) in
  let tb = hd clist and bt = hd(tl clist) in
  let T = `T` and F = `F` in
  fun tm ->
    try let l,r = (I F_F check) (dest_eq tm) in
        if l = r then EQT_INTRO (REFL l) else
        if l = T then SPEC r tb else
        if r = T then SPEC l bt else fail()
    with Failure _ -> failwith "bool_EQ_CONV";;

let COND_CONV =
  let T = `T` and F = `F` and vt = genvar`:A` and vf = genvar `:A` in
  let gen = GENL [vt;vf] in
  let CT,CF = (gen F_F gen) (CONJ_PAIR (SPECL [vt;vf] COND_CLAUSES)) in
  fun tm ->
    let P,(u,v) = try dest_cond tm
                  with Failure _ -> failwith "COND_CONV: not a conditional" in
    let ty = type_of u in
    if (P=T) then SPEC v (SPEC u (INST_TYPE [ty,`:A`] CT)) else
    if (P=F) then SPEC v (SPEC u (INST_TYPE [ty,`:A`] CF)) else
    if (u=v) then SPEC u (SPEC P (INST_TYPE [ty,`:A`] COND_ID)) else
    if (aconv u v) then
       let cnd = AP_TERM (rator tm) (ALPHA v u) in
       let thm = SPEC u (SPEC P (INST_TYPE [ty,`:A`] COND_ID)) in
           TRANS cnd thm else
  failwith "COND_CONV: can't simplify conditional";;

let SUBST_MATCH eqth th =
 let tm_inst,ty_inst = find_match (lhs(concl eqth)) (concl th) in
 SUBS [INST tm_inst (INST_TYPE ty_inst eqth)] th;;

let SUBST thl pat th =
  let eqs,vs = unzip thl in
  let gvs = map (genvar o type_of) vs in
  let gpat = subst (zip gvs vs) pat in
  let ls,rs = unzip (map (dest_eq o concl) eqs) in
  let ths = map (ASSUME o mk_eq) (zip gvs rs) in
  let th1 = ASSUME gpat in
  let th2 = SUBS ths th1 in
  let th3 = itlist DISCH (map concl ths) (DISCH gpat th2) in
  let th4 = INST (zip ls gvs) th3 in
  MP (rev_itlist (C MP) eqs th4) th;;

(* let GSUBS = ...                                                           *)
(* let SUBS_OCCS = ...                                                       *)

(* A poor thing but mine own. The old ones use mk_thm and the commented
   out functions are bogus. *)

let SUBST_CONV thvars template tm =
  let thms,vars = unzip thvars in
  let gvs = map (genvar o type_of) vars in
  let gtemplate = subst (zip gvs vars) template in
  SUBST (zip thms gvs) (mk_eq(template,gtemplate)) (REFL tm);;

(* ------------------------------------------------------------------------- *)
(* Filtering rewrites.                                                       *)
(* ------------------------------------------------------------------------- *)

let FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_ASM_REWRITE_RULE f thl th =
    REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_ONCE_ASM_REWRITE_RULE f thl th =
    ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th;;

let (FILTER_PURE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    PURE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_PURE_ONCE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    PURE_ONCE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_ONCE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    ONCE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Tacticals.                                                                *)
(* ------------------------------------------------------------------------- *)

let (X_CASES_THENL: term list list -> thm_tactic list -> thm_tactic) =
  fun varsl ttacl ->
    end_itlist DISJ_CASES_THEN2
       (map (fun (vars,ttac) -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac)
        (zip varsl ttacl));;

let (X_CASES_THEN: term list list -> thm_tactical) =
  fun varsl ttac ->
    end_itlist DISJ_CASES_THEN2
       (map (fun vars -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl);;

let (CASES_THENL: thm_tactic list -> thm_tactic) =
  fun ttacl -> end_itlist DISJ_CASES_THEN2 (map (REPEAT_TCL CHOOSE_THEN) ttacl);;

(* ------------------------------------------------------------------------- *)
(* Tactics.                                                                  *)
(* ------------------------------------------------------------------------- *)

let (DISCARD_TAC: thm_tactic) =
  let truth = `T` in
  fun th (asl,w) ->
    if exists (aconv (concl th)) (truth::(map (concl o snd) asl))
    then ALL_TAC (asl,w)
    else failwith "DISCARD_TAC";;

let (CHECK_ASSUME_TAC: thm_tactic) =
  fun gth ->
    FIRST [CONTR_TAC gth;  ACCEPT_TAC gth;
           DISCARD_TAC gth; ASSUME_TAC gth];;

let (FILTER_GEN_TAC: term -> tactic) =
  fun tm (asl,w) ->
    if is_forall w & not (tm = fst(dest_forall w)) then
        GEN_TAC (asl,w)
    else failwith "FILTER_GEN_TAC";;

let (FILTER_DISCH_THEN: thm_tactic -> term -> tactic) =
  fun ttac tm (asl,w) ->
    if is_neg_imp w & not (free_in tm (fst(dest_neg_imp w))) then
      DISCH_THEN ttac (asl,w)
    else failwith "FILTER_DISCH_THEN";;

let FILTER_STRIP_THEN ttac tm =
  FIRST [FILTER_GEN_TAC tm; FILTER_DISCH_THEN ttac tm; CONJ_TAC];;

let FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_ASSUME_TAC;;

let FILTER_STRIP_TAC = FILTER_STRIP_THEN STRIP_ASSUME_TAC;;

(* ------------------------------------------------------------------------- *)
(* Conversions for quantifier movement using proforma theorems.              *)
(* ------------------------------------------------------------------------- *)

(* let ....... *)

(* ------------------------------------------------------------------------- *)
(* Resolution stuff.                                                         *)
(* ------------------------------------------------------------------------- *)

let RES_CANON =
    let not_elim th =
      if is_neg (concl th) then true,(NOT_ELIM th) else (false,th) in
    let rec canon fl th =
       let w = concl th in
       if (is_conj w) then
          let (th1,th2) = CONJ_PAIR th in (canon fl th1) @ (canon fl th2) else
       if ((is_imp w) & not(is_neg w)) then
          let ante,conc = dest_neg_imp w in
          if (is_conj ante) then
             let a,b = dest_conj ante in
             let cth = NOT_MP th (CONJ (ASSUME a) (ASSUME b)) in
             let th1 = DISCH b cth and th2 = DISCH a cth in
                 (canon true (DISCH a th1)) @ (canon true (DISCH b th2)) else
          if (is_disj ante) then
             let a,b = dest_disj ante in
             let ath = DISJ1 (ASSUME a) b and bth = DISJ2 a (ASSUME b) in
             let th1 = DISCH a (NOT_MP th ath) and
                 th2 = DISCH b (NOT_MP th bth) in
                 (canon true th1) @ (canon true th2) else
          if (is_exists ante) then
             let v,body = dest_exists ante in
             let newv = variant (thm_frees th) v in
             let newa = subst [newv,v] body in
             let th1 = NOT_MP th (EXISTS (ante, newv) (ASSUME newa)) in
                 canon true (DISCH newa th1) else
             map (GEN_ALL o (DISCH ante)) (canon true (UNDISCH th)) else
       if (is_eq w & (type_of (rand w) = `:bool`)) then
          let (th1,th2) = EQ_IMP_RULE th in
          (if fl then [GEN_ALL th] else []) @ (canon true th1) @ (canon true th2) else
       if (is_forall w) then
           let vs,body = strip_forall w in
           let fvs = thm_frees th in
           let vfn = fun l -> variant (l @ fvs) in
           let nvs = itlist (fun v nv -> let v' = vfn nv v in (v'::nv)) vs [] in
               canon fl (SPECL nvs th) else
       if fl then [GEN_ALL th] else [] in
    fun th -> try let args = map (not_elim o SPEC_ALL) (CONJUNCTS (SPEC_ALL th)) in
                  let imps = flat (map (map GEN_ALL o (uncurry canon)) args) in
                  check (fun l -> l <> []) imps
              with Failure _ ->
                failwith "RES_CANON: no implication is derivable from input thm.";;

let IMP_RES_THEN,RES_THEN =
  let MATCH_MP impth =
      let sth = SPEC_ALL impth in
      let matchfn = (fun (a,b,c) -> b,c) o
                    term_match [] (fst(dest_neg_imp(concl sth))) in
         fun th -> NOT_MP (INST_TY_TERM (matchfn (concl th)) sth) th in
  let check st l = (if l = [] then failwith st else l) in
  let IMP_RES_THEN ttac impth =
      let ths = try RES_CANON impth with Failure _ -> failwith "IMP_RES_THEN: no implication" in
      ASSUM_LIST
       (fun asl ->
        let l = itlist (fun th -> (@) (mapfilter (MATCH_MP th) asl)) ths [] in
        let res = check "IMP_RES_THEN: no resolvents " l in
        let tacs = check "IMP_RES_THEN: no tactics" (mapfilter ttac res) in
        EVERY tacs) in
  let RES_THEN ttac (asl,g) =
      let asm = map snd asl in
      let ths = itlist (@) (mapfilter RES_CANON asm) [] in
      let imps = check "RES_THEN: no implication" ths in
      let l = itlist (fun th -> (@) (mapfilter (MATCH_MP th) asm)) imps [] in
      let res = check "RES_THEN: no resolvents " l in
      let tacs = check "RES_THEN: no tactics" (mapfilter ttac res) in
          EVERY tacs (asl,g) in
  IMP_RES_THEN,RES_THEN;;

let IMP_RES_TAC th g =
  try IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th g
  with Failure _ -> ALL_TAC g;;

let RES_TAC g =
  try RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) g
  with Failure _ -> ALL_TAC g;;

(* ------------------------------------------------------------------------- *)
(* Stuff for handling type definitions.                                      *)
(* ------------------------------------------------------------------------- *)

let prove_rep_fn_one_one th =
  try let thm = CONJUNCT1 th in
      let A,R = (I F_F rator) (dest_comb(lhs(snd(dest_forall(concl thm))))) in
      let _,[aty;rty] = dest_type (type_of R) in
      let a = mk_primed_var("a",aty) in let a' = variant [a] a in
      let a_eq_a' = mk_eq(a,a') and
          Ra_eq_Ra' = mk_eq(mk_comb(R,a),mk_comb (R,a')) in
      let th1 = AP_TERM A (ASSUME Ra_eq_Ra') in
      let ga1 = genvar aty and ga2 = genvar aty in
      let th2 = SUBST [SPEC a thm,ga1;SPEC a' thm,ga2] (mk_eq(ga1,ga2)) th1 in
      let th3 = DISCH a_eq_a' (AP_TERM R (ASSUME a_eq_a')) in
          GEN a (GEN a' (IMP_ANTISYM_RULE (DISCH Ra_eq_Ra' th2) th3))
  with Failure _ -> failwith "prove_rep_fn_one_one";;

let prove_rep_fn_onto th =
  try let [th1;th2] = CONJUNCTS th in
      let r,eq = (I F_F rhs)(dest_forall(concl th2)) in
      let RE,ar = dest_comb(lhs eq) and
          sr = (mk_eq o (fun (x,y) -> y,x) o dest_eq) eq in
      let a = mk_primed_var ("a",type_of ar) in
      let sra = mk_eq(r,mk_comb(RE,a)) in
      let ex = mk_exists(a,sra) in
      let imp1 = EXISTS (ex,ar) (SYM(ASSUME eq)) in
      let v = genvar (type_of r) and
          A = rator ar and
          s' = AP_TERM RE (SPEC a th1) in
      let th = SUBST[SYM(ASSUME sra),v](mk_eq(mk_comb(RE,mk_comb(A,v)),v))s' in
      let imp2 = CHOOSE (a,ASSUME ex) th in
      let swap = IMP_ANTISYM_RULE (DISCH eq imp1) (DISCH ex imp2) in
          GEN r (TRANS (SPEC r th2) swap)
  with Failure _ -> failwith "prove_rep_fn_onto";;

let prove_abs_fn_onto th =
  try let [th1;th2] = CONJUNCTS th in
      let a,(A,R) = (I F_F ((I F_F rator)o dest_comb o lhs))
        (dest_forall(concl th1)) in
      let thm1 = EQT_ELIM(TRANS (SPEC (mk_comb (R,a)) th2)
                                (EQT_INTRO (AP_TERM R (SPEC a th1)))) in
      let thm2 = SYM(SPEC a th1) in
      let r,P = (I F_F (rator o lhs)) (dest_forall(concl th2)) in
      let ex = mk_exists(r,mk_conj(mk_eq(a,mk_comb(A,r)),mk_comb(P,r))) in
          GEN a (EXISTS(ex,mk_comb(R,a)) (CONJ thm2 thm1))
  with Failure _ -> failwith "prove_abs_fn_onto";;

let prove_abs_fn_one_one th =
  try let [th1;th2] = CONJUNCTS th in
      let r,P = (I F_F (rator o lhs)) (dest_forall(concl th2)) and
          A,R = (I F_F rator) (dest_comb(lhs(snd(dest_forall(concl th1))))) in
      let r' = variant [r] r in
      let as1 = ASSUME(mk_comb(P,r)) and as2 = ASSUME(mk_comb(P,r')) in
      let t1 = EQ_MP (SPEC r th2) as1 and t2 = EQ_MP (SPEC r' th2) as2 in
      let eq = (mk_eq(mk_comb(A,r),mk_comb(A,r'))) in
      let v1 = genvar(type_of r) and v2 = genvar(type_of r) in
      let i1 = DISCH eq
               (SUBST [t1,v1;t2,v2] (mk_eq(v1,v2)) (AP_TERM R (ASSUME eq))) and
          i2 = DISCH (mk_eq(r,r')) (AP_TERM A (ASSUME (mk_eq(r,r')))) in
      let thm = IMP_ANTISYM_RULE i1 i2 in
      let disch =  DISCH (mk_comb(P,r)) (DISCH (mk_comb(P,r')) thm) in
          GEN r (GEN r' disch)
  with Failure _ -> failwith "prove_abs_fn_one_one";;

(* ------------------------------------------------------------------------- *)
(* AC rewriting needs to be wrapped up as a special conversion.              *)
(* ------------------------------------------------------------------------- *)

let AC_CONV(assoc,sym) =
  let th1 = SPEC_ALL assoc
  and th2 = SPEC_ALL sym in
  let th3 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [th2] th1 in
  let th4 = SYM th1 in
  let th5 = GEN_REWRITE_RULE RAND_CONV [th4] th3 in
  EQT_INTRO o AC(end_itlist CONJ [th2; th4; th5]);;

let AC_RULE ths = EQT_ELIM o AC_CONV ths;;

(* ------------------------------------------------------------------------- *)
(* The order of picking conditionals is different!                           *)
(* ------------------------------------------------------------------------- *)

let (COND_CASES_TAC :tactic) =
    let is_good_cond tm =
      try not(is_const(fst(dest_cond tm)))
      with Failure _ -> false in
    fun (asl,w) ->
      let cond = find_term (fun tm -> is_good_cond tm & free_in tm w) w in
      let p,(t,u) = dest_cond cond in
      let inst = INST_TYPE [type_of t, `:A`] COND_CLAUSES in
      let (ct,cf) = CONJ_PAIR (SPEC u (SPEC t inst)) in
      DISJ_CASES_THEN2
         (fun th -> SUBST1_TAC (EQT_INTRO th) THEN
               SUBST1_TAC ct THEN ASSUME_TAC th)
         (fun th -> SUBST1_TAC (EQF_INTRO th) THEN
               SUBST1_TAC cf THEN ASSUME_TAC th)
         (SPEC p EXCLUDED_MIDDLE)
         (asl,w) ;;

(* ------------------------------------------------------------------------- *)
(* MATCH_MP_TAC allows universals on the right of implication.               *)
(* Here's a crude hack to allow it.                                          *)
(* ------------------------------------------------------------------------- *)

let MATCH_MP_TAC th =
  MATCH_MP_TAC th ORELSE
  MATCH_MP_TAC(PURE_REWRITE_RULE[RIGHT_IMP_FORALL_THM] th);;

(* ------------------------------------------------------------------------- *)
(* Various theorems have different names.                                    *)
(* ------------------------------------------------------------------------- *)

let ZERO_LESS_EQ = LE_0;;

let LESS_EQ_MONO = LE_SUC;;

let NOT_LESS = NOT_LT;;

let LESS_0 = LT_0;;

let LESS_EQ_REFL = LE_REFL;;

let LESS_EQUAL_ANTISYM = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_ANTISYM)));;

let NOT_LESS_0 = GEN_ALL(EQF_ELIM(SPEC_ALL(CONJUNCT1 LT)));;

let LESS_TRANS = LT_TRANS;;

let LESS_LEMMA1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL(CONJUNCT2 LT))));;

let LESS_SUC_REFL = prove(`!n. n < SUC n`,REWRITE_TAC[LT]);;

let FACT_LESS = FACT_LT;;

let LESS_EQ_SUC_REFL = prove(`!n. n <= SUC n`,REWRITE_TAC[LE; LE_REFL]);;

let LESS_EQ_ADD = LE_ADD;;

let GREATER_EQ = GE;;

let LESS_EQUAL_ADD = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_EXISTS)));;

let LESS_EQ_IMP_LESS_SUC = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_SUC_LE)));;

let LESS_IMP_LESS_OR_EQ = LT_IMP_LE;;

let LESS_MONO_ADD = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_ADD_RCANCEL)));;

let LESS_SUC = prove(`!m n. m < n ==> m < (SUC n)`,MESON_TAC[LT]);;

let LESS_CASES = LTE_CASES;;

let LESS_EQ = GSYM LE_SUC_LT;;

let LESS_OR_EQ = LE_LT;;

let LESS_ADD_1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL
    (REWRITE_RULE[ADD1] LT_EXISTS))));;

let SUC_SUB1 = prove(`!m. SUC m - 1 = m`,
                     REWRITE_TAC[num_CONV `1`; SUB_SUC; SUB_0]);;

let LESS_MONO_EQ = LT_SUC;;

let LESS_ADD_SUC = prove (`!m n. m < m + SUC n`,
                          REWRITE_TAC[ADD_CLAUSES; LT_SUC_LE; LE_ADD]);;

let LESS_REFL = LT_REFL;;

let INV_SUC_EQ = SUC_INJ;;

let LESS_EQ_CASES = LE_CASES;;

let LESS_EQ_TRANS = LE_TRANS;;

let LESS_THM = CONJUNCT2 LT;;

let GREATER = GT;;

let LESS_EQ_0 = CONJUNCT1 LE;;

let OR_LESS = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_SUC_LT)));;

let SUB_EQUAL_0 = SUB_REFL;;

let SUB_MONO_EQ = SUB_SUC;;

let NOT_SUC_LESS_EQ = prove (`!n m. ~(SUC n <= m) <=> m <= n`,
                             REWRITE_TAC[NOT_LE; LT] THEN
                             MESON_TAC[LE_LT]);;

let SUC_NOT = GSYM NOT_SUC;;

let LESS_LESS_CASES = prove(`!m n:num. (m = n) \/ m < n \/ n < m`,
                            MESON_TAC[LT_CASES]);;

let NOT_LESS_EQUAL = NOT_LE;;

let LESS_EQ_EXISTS = LE_EXISTS;;

let LESS_MONO_ADD_EQ = LT_ADD_RCANCEL;;

let LESS_LESS_EQ_TRANS = LTE_TRANS;;

let SUB_SUB = ARITH_RULE
  `!b c. c <= b ==> (!a:num. a - (b - c) = (a + c) - b)`;;

let LESS_CASES_IMP = ARITH_RULE
  `!m n:num. ~(m < n) /\ ~(m = n) ==> n < m`;;

let SUB_LESS_EQ = ARITH_RULE
  `!n m:num. (n - m) <= n`;;

let SUB_EQ_EQ_0 = ARITH_RULE
 `!m n:num. (m - n = m) <=> (m = 0) \/ (n = 0)`;;

let SUB_LEFT_LESS_EQ = ARITH_RULE
  `!m n p:num. m <= (n - p) <=> (m + p) <= n \/ m <= 0`;;

let SUB_LEFT_GREATER_EQ =
  ARITH_RULE `!m n p:num. m >= (n - p) <=> (m + p) >= n`;;

let LESS_EQ_LESS_TRANS = LET_TRANS;;

let LESS_0_CASES = ARITH_RULE `!m. (0 = m) \/ 0 < m`;;

let LESS_OR = ARITH_RULE `!m n. m < n ==> (SUC m) <= n`;;

let SUB = ARITH_RULE
  `(!m. 0 - m = 0) /\
   (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))`;;

let LESS_MULT_MONO = prove
 (`!m i n. ((SUC n) * m) < ((SUC n) * i) <=> m < i`,
  REWRITE_TAC[LT_MULT_LCANCEL; NOT_SUC]);;

let LESS_MONO_MULT = prove
 (`!m n p. m <= n ==> (m * p) <= (n * p)`,
  SIMP_TAC[LE_MULT_RCANCEL]);;

let LESS_MULT2 = prove
 (`!m n. 0 < m /\ 0 < n ==> 0 < (m * n)`,
  REWRITE_TAC[LT_MULT]);;

let SUBSET_FINITE = prove
 (`!s. FINITE s ==> (!t. t SUBSET s ==> FINITE t)`,
  MESON_TAC[FINITE_SUBSET]);;

let LESS_EQ_SUC = prove
 (`!n. m <= SUC n <=> (m = SUC n) \/ m <= n`,
  REWRITE_TAC[LE]);;

let ANTE_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP t th));;

let IMP_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP th t));;

(* ------------------------------------------------------------------------ *)
(* Set theory lemmas.                                                       *)
(* ------------------------------------------------------------------------ *)

let INFINITE_MEMBER = prove(
  `!s. INFINITE(s:A->bool) ==> ?x. x IN s`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(s:A->bool = {})` MP_TAC THENL
   [UNDISCH_TAC `INFINITE (s:A->bool)` THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INFINITE; FINITE_EMPTY];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
    PURE_ONCE_REWRITE_TAC[NOT_FORALL_THM] THEN
    REWRITE_TAC[]]);;

let INFINITE_CHOOSE = prove(
  `!s:A->bool. INFINITE(s) ==> ((@) s) IN s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_MEMBER) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[IN] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]);;

let INFINITE_DELETE = prove(
  `!(t:A->bool) x. INFINITE (t DELETE x) = INFINITE(t)`,
  REWRITE_TAC[INFINITE; FINITE_DELETE]);;

let INFINITE_INSERT = prove(
  `!(x:A) t. INFINITE(x INSERT t) = INFINITE(t)`,
  REWRITE_TAC[INFINITE; FINITE_INSERT]);;

let SIZE_INSERT = prove(
  `!(x:A) t. ~(x IN t) /\ t HAS_SIZE n ==> (x INSERT t) HAS_SIZE (SUC n)`,
  SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_RULES]);;

let SIZE_DELETE = prove(
  `!(x:A) t. x IN t /\ t HAS_SIZE (SUC n) ==> (t DELETE x) HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE_SUC]);;

let SIZE_EXISTS = prove(
  `!s N. s HAS_SIZE (SUC N) ==> ?x:A. x IN s`,
  SIMP_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY]);;

let SUBSET_DELETE = prove(
  `!s t (x:A). s SUBSET t ==> (s DELETE x) SUBSET t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET]);;

let INFINITE_FINITE_CHOICE = prove(
  `!n (s:A->bool). INFINITE(s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN
    REWRITE_TAC[HAS_SIZE; EMPTY_SUBSET; HAS_SIZE_0];
    FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `s DELETE ((@) s :A)`) THEN
    ASM_REWRITE_TAC[INFINITE_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `((@) s :A) INSERT t` THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
        GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        REWRITE_TAC[IN_DELETE] THEN CONV_TAC(EQT_INTRO o TAUT)];
        MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN UNDISCH_TAC `t SUBSET (s DELETE ((@) s:A))` THEN
        REWRITE_TAC[SUBSET; IN_DELETE] THEN
        DISCH_THEN(IMP_RES_THEN MP_TAC) THEN REWRITE_TAC[]]]);;

let IMAGE_WOP_LEMMA = prove(
  `!N (t:num->bool) (u:A->bool).
        u SUBSET (IMAGE f t) /\ u HAS_SIZE (SUC N) ==>
        ?n v. (u = (f n) INSERT v) /\
              !y. y IN v ==> ?m. (y = f m) /\ n < m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\n:num. ?y:A. y IN u /\ (y = f n)` num_WOP) THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:A` o MATCH_MP SIZE_EXISTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:A` o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
       funpow 2 (fst o dest_imp) o snd) THENL
   [MAP_EVERY EXISTS_TAC [`n:num`; `y:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `u DELETE (x:A)`] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INSERT_DELETE THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:A` o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[GSYM NOT_LESS_EQUAL] THEN
    REWRITE_TAC[LESS_OR_EQ; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [DISCH_THEN(ANTE_RES_THEN (MP_TAC o CONV_RULE NOT_EXISTS_CONV)) THEN
      DISCH_THEN(MP_TAC o SPEC `z:A`) THEN REWRITE_TAC[] THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(z:A = x)` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------ *)
(* Lemma about finite colouring of natural numbers.                         *)
(* ------------------------------------------------------------------------ *)

let COLOURING_LEMMA = prove(
  `!M col s. (INFINITE(s) /\ !n:A. n IN s ==> col(n) <= M) ==>
          ?c t. t SUBSET s /\ INFINITE(t) /\ !n:A. n IN t ==> (col(n) = c)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LESS_EQ_0] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `s:A->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `INFINITE { x:A | x IN s /\ (col x = SUC M) } \/
      INFINITE { x:A | x IN s /\ col x <= M}`
    DISJ_CASES_TAC THENL
     [UNDISCH_TAC `INFINITE(s:A->bool)` THEN
      REWRITE_TAC[INFINITE; GSYM DE_MORGAN_THM; GSYM FINITE_UNION] THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP SUBSET_FINITE) THEN
      REWRITE_TAC[SUBSET; IN_UNION] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM LESS_EQ_SUC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`SUC M`; `{ x:A | x IN s /\ (col x = SUC M)}`] THEN
      ASM_REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `!n:A. n IN { x | x IN s /\ col x <= M } ==> col(n) <= M`
      MP_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT2);
        FIRST_X_ASSUM(MP_TAC o SPECL [`col:A->num`;
                                        `{ x:A | x IN s /\ col x <= M}`]) THEN
        ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC(TAUT `(c ==> d) ==> (b ==> c) ==> b ==> d`) THEN
        DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_TAC `t:A->bool`)) THEN
        MAP_EVERY EXISTS_TAC [`c:num`; `t:A->bool`] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `{ x:A | x IN s /\ col x <= M }` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]]);;

let COLOURING_THM = prove(
  `!M col. (!n. col n <= M) ==>
           ?c s. INFINITE(s) /\ !n:num. n IN s ==> (col(n) = c)`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`M:num`; `col:num->num`; `UNIV:num->bool`] COLOURING_LEMMA) THEN
  ASM_REWRITE_TAC[num_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_TAC `t:num->bool`)) THEN
  MAP_EVERY EXISTS_TAC [`c:num`; `t:num->bool`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Simple approach via lemmas then induction over size of coloured sets.    *)
(* ------------------------------------------------------------------------ *)

let RAMSEY_LEMMA1 = prove(
 `(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
         ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                   (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~(((@) s) IN t) /\
                      (!u. u SUBSET t /\ u HAS_SIZE N
                           ==> (C(((@) s) INSERT u) = c))`,
  DISCH_THEN((THEN) (REPEAT STRIP_TAC) o MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `\u. C (((@) s :A) INSERT u):num`) THEN
  DISCH_THEN(MP_TAC o SPEC `s DELETE ((@)s:A)`) THEN BETA_TAC THEN
  ASM_REWRITE_TAC[INFINITE_DELETE] THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
        funpow 2 (fst o dest_imp) o snd) THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `t SUBSET (s DELETE ((@) s :A))` THEN
      REWRITE_TAC[SUBSET; IN_INSERT; IN_DELETE; NOT_IN_EMPTY] THEN
      DISCH_TAC THEN GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC INFINITE_CHOOSE;
        FIRST_ASSUM(ANTE_RES_THEN ASSUME_TAC)] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `t SUBSET (s DELETE ((@) s :A))` THEN
      ASM_REWRITE_TAC[SUBSET; IN_DELETE] THEN
      DISCH_THEN(MP_TAC o SPEC `(@)s:A`) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`t:A->bool`; `c:num`] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_DELETE]) THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN
      GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN(fun th -> REWRITE_TAC[th]));
      DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[]]]);;

let RAMSEY_LEMMA2 = prove(
 `(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~(((@) s) IN t) /\
                  (!u. u SUBSET t /\ u HAS_SIZE N
                       ==> (C(((@) s) INSERT u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t x col. (!n. col n <= M) /\
                          (!n. (t n) SUBSET s) /\
                          (!n. t(SUC n) SUBSET (t n)) /\
                          (!n. ~((x n) IN (t n))) /\
                          (!n. x(SUC n) IN (t n)) /\
                          (!n. (x n) IN s) /\
                          (!n u. u SUBSET (t n) /\ u HAS_SIZE N
                                 ==> (C((x n) INSERT u) = col n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `\s (n:num). @t:A->bool. ?c:num.
      INFINITE(t) /\
      t SUBSET s /\
      ~(((@) s) IN t) /\
      !u. u SUBSET t /\ u HAS_SIZE N ==> (C(((@) s) INSERT u) = c)`]
    num_Axiom) THEN DISCH_THEN(MP_TAC o BETA_RULE o EXISTENCE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(A->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n:num. (f n) SUBSET (s:A->bool) /\
    ?c. INFINITE(f(SUC n)) /\ f(SUC n) SUBSET (f n) /\
        ~(((@)(f n)) IN (f(SUC n))) /\
        !u. u SUBSET (f(SUC n)) /\ u HAS_SIZE N ==>
          (C(((@)(f n)) INSERT u) = c:num)`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      FIRST_ASSUM(SUBST1_TAC o SPEC `0`) THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `f(n:num):A->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      FIRST_ASSUM(SUBST1_TAC o SPEC `SUC n`) THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
      TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC SUBSET_TRANS THEN
        FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
        CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC])) THEN
      MATCH_ACCEPT_TAC SUBSET_REFL];
    PURE_REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM;
                     FORALL_AND_THM] THEN
    DISCH_THEN(REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_TAC `col:num->num` o CONV_RULE SKOLEM_CONV) THEN
    MAP_EVERY EXISTS_TAC
      [`\n:num. f(SUC n):A->bool`; `\n:num. (@)(f n):A`] THEN
    BETA_TAC THEN EXISTS_TAC `col:num->num` THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP INFINITE_FINITE_CHOICE o SPEC `n:num`) THEN
      DISCH_THEN(CHOOSE_THEN MP_TAC o SPEC `N:num`) THEN
      DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
          ANTE_RES_THEN MP_TAC th) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          EXISTS_TAC `n:num` THEN MATCH_MP_TAC INFINITE_CHOOSE THEN
          SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
          TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `f(SUC n):A->bool` THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `!n:num. ~(((@)(f n):A) IN (f(SUC n)))` THEN
        DISCH_THEN(MP_TAC o SPEC `n:num`) THEN CONV_TAC CONTRAPOS_CONV THEN
        REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_ACCEPT_TAC o REWRITE_RULE[SUBSET])];
      REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
       [GEN_TAC; INDUCT_TAC THENL
         [ASM_REWRITE_TAC[];
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          EXISTS_TAC `SUC n`]] THEN
      MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC[]]]);;

let RAMSEY_LEMMA3 = prove(
 `(!C s. INFINITE(s:A->bool) /\
             (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
             ==> ?t x col. (!n. col n <= M) /\
                           (!n. (t n) SUBSET s) /\
                           (!n. t(SUC n) SUBSET (t n)) /\
                           (!n. ~((x n) IN (t n))) /\
                           (!n. x(SUC n) IN (t n)) /\
                           (!n. (x n) IN s) /\
                           (!n u. u SUBSET (t n) /\ u HAS_SIZE N
                                  ==> (C((x n) INSERT u) = col n)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                      (!u. u SUBSET t /\ u HAS_SIZE (SUC N) ==> (C(u) = c))`,
  DISCH_THEN((THEN) (REPEAT STRIP_TAC) o MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:(A->bool)->num`; `s:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->(A->bool)` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->A` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `col:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`M:num`; `col:num->num`; `UNIV:num->bool`]
    COLOURING_LEMMA) THEN ASM_REWRITE_TAC[num_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (x:num->A) t`; `c:num`] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (t n:A->bool) SUBSET (t m)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t(m + d):A->bool` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (x n:A) IN (t m)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `m + d`]) THEN
    REWRITE_TAC[LESS_EQ_ADD; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM ADD1; ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. ((x:num->A) m = x n) <=> (m = n)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (SPECL [`m:num`; `n:num`] LESS_LESS_CASES) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      FIRST_ASSUM(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `INFINITE(t:num->bool)` THEN
    MATCH_MP_TAC INFINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN GEN_TAC THEN
    DISCH_THEN(CHOOSE_THEN (SUBST1_TAC o CONJUNCT1)) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o MATCH_MP IMAGE_WOP_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `v:A->bool` MP_TAC)) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c = (col:num->num) n` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `u SUBSET (IMAGE (x:num->A) t)` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `(x:num->A) n`) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN
      DISCH_THEN(CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN GEN_TAC THEN
        DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `v = u DELETE ((x:num->A) n)` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[] THEN REWRITE_TAC[DELETE_INSERT] THEN
          REWRITE_TAC[EXTENSION; IN_DELETE;
            TAUT `(a <=> a /\ b) <=> a ==> b`] THEN
          GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
          ASM_REWRITE_TAC[LESS_REFL];
          MATCH_MP_TAC SIZE_DELETE THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[IN_INSERT]; FIRST_ASSUM MATCH_ACCEPT_TAC]]]]]);;

let RAMSEY = prove(
  `!M N C s.
        INFINITE(s:A->bool) /\
        (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                  (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:A->bool`; `(C:(A->bool)->num) {}`] THEN
    ASM_REWRITE_TAC[HAS_SIZE_0] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    MAP_EVERY MATCH_MP_TAC [RAMSEY_LEMMA3; RAMSEY_LEMMA2; RAMSEY_LEMMA1] THEN
    POP_ASSUM MATCH_ACCEPT_TAC]);;
