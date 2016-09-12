(* ========================================================================= *)
(* A HOL "by" tactic, doing Mizar-like things, trying something that is      *)
(* sufficient for HOL's basic rules, trying a few other things like          *)
(* arithmetic, and finally if all else fails using MESON_TAC[].              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* More refined net lookup that double-checks conditions like matchability.  *)
(* ------------------------------------------------------------------------- *)

let matching_enter tm y net =
  enter [] (tm,((fun tm' -> can (term_match [] tm) tm'),y)) net;;

let unconditional_enter (tm,y) net =
  enter [] (tm,((fun t -> true),y)) net;;

let conditional_enter (tm,condy) net =
  enter [] (tm,condy) net;;

let careful_lookup tm net =
  map snd (filter (fun (c,y) -> c tm) (lookup tm net));;

(* ------------------------------------------------------------------------- *)
(* Transform theorem list to simplify, eliminate redundant connectives and   *)
(* split the problem into (generally multiple) subproblems. Then, call the   *)
(* prover given as the first argument on each component.                     *)
(* ------------------------------------------------------------------------- *)

let SPLIT_THEN =
  let action_false th f oths = th
  and action_true th f oths = f oths
  and action_conj th f oths =
    f (CONJUNCT1 th :: CONJUNCT2 th :: oths)
  and action_disj th f oths =
    let th1 = f (ASSUME(lhand(concl th)) :: oths)
    and th2 = f (ASSUME(rand(concl th)) :: oths) in
    DISJ_CASES th th1 th2
  and action_taut tm =
    let pfun = PART_MATCH lhs (TAUT tm) in
    let prule th = EQ_MP (pfun (concl th)) th in
    lhand tm,(fun th f oths -> f(prule th :: oths)) in
  let enet = itlist unconditional_enter
    [`F`,action_false;
     `T`,action_true;
     `p /\ q`,action_conj;
     `p \/ q`,action_disj;
     action_taut `(p ==> q) <=> ~p \/ q`;
     action_taut `~F <=> T`;
     action_taut `~T <=> F`;
     action_taut  `~(~p) <=> p`;
     action_taut  `~(p /\ q) <=> ~p \/ ~q`;
     action_taut  `~(p \/ q) <=> ~p /\ ~q`;
     action_taut  `~(p ==> q) <=> p /\ ~q`;
     action_taut `p /\ F <=> F`;
     action_taut `F /\ p <=> F`;
     action_taut `p /\ T <=> p`;
     action_taut `T /\ p <=> p`;
     action_taut `p \/ F <=> p`;
     action_taut `F \/ p <=> p`;
     action_taut `p \/ T <=> T`;
     action_taut `T \/ p <=> T`]
    (let tm,act = action_taut `~(p <=> q) <=> p /\ ~q \/ ~p /\ q` in
     let cond tm = type_of(rand(rand tm)) = bool_ty in
     conditional_enter (tm,(cond,act))
        (let tm,act = action_taut `(p <=> q) <=> p /\ q \/ ~p /\ ~q` in
         let cond tm = type_of(rand tm) = bool_ty in
         conditional_enter (tm,(cond,act)) empty_net)) in
  fun prover ->
    let rec splitthen splat tosplit =
      match tosplit with
        [] -> prover (rev splat)
      | th::oths ->
          let funs = careful_lookup (concl th) enet in
          if funs = [] then splitthen (th::splat) oths
          else (hd funs) th (splitthen splat) oths in
    splitthen [];;

(* ------------------------------------------------------------------------- *)
(* A similar thing that also introduces Skolem constants (but not functions) *)
(* and does some slight first-order simplification like trivial miniscoping. *)
(* ------------------------------------------------------------------------- *)

let SPLIT_FOL_THEN =
  let action_false th f splat oths = th
  and action_true th f splat oths = f oths
  and action_conj th f splat oths =
    f (CONJUNCT1 th :: CONJUNCT2 th :: oths)
  and action_disj th f splat oths =
    let th1 = f (ASSUME(lhand(concl th)) :: oths)
    and th2 = f (ASSUME(rand(concl th)) :: oths) in
    DISJ_CASES th th1 th2
  and action_exists th f splat oths =
    let v,bod = dest_exists(concl th) in
    let vars = itlist (union o thm_frees) (oths @ splat) (thm_frees th) in
    let v' = variant vars v in
    let th' = ASSUME (subst [v',v] bod) in
    CHOOSE (v',th) (f (th'::oths))
  and action_taut tm =
    let pfun = PART_MATCH lhs (TAUT tm) in
    let prule th = EQ_MP (pfun (concl th)) th in
    lhand tm,(fun th f splat oths -> f(prule th :: oths))
  and action_fol tm =
    let pfun = PART_MATCH lhs (prove(tm,MESON_TAC[])) in
    let prule th = EQ_MP (pfun (concl th)) th in
    lhand tm,(fun th f splat oths -> f(prule th :: oths)) in
  let enet = itlist unconditional_enter
    [`F`,action_false;
     `T`,action_true;
     `p /\ q`,action_conj;
     `p \/ q`,action_disj;
     `?x. P x`,action_exists;
     action_taut `~(~p) <=> p`;
     action_taut `~(p /\ q) <=> ~p \/ ~q`;
     action_taut `~(p \/ q) <=> ~p /\ ~q`;
     action_fol `~(!x. P x) <=> (?x. ~(P x))`;
     action_fol `(!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)`]
    empty_net in
  fun prover ->
    let rec splitthen splat tosplit =
      match tosplit with
        [] -> prover (rev splat)
      | th::oths ->
          let funs = careful_lookup (concl th) enet in
          if funs = [] then splitthen (th::splat) oths
          else (hd funs) th (splitthen splat) splat oths in
    splitthen [];;

(* ------------------------------------------------------------------------- *)
(* Do the basic "semantic correlates" stuff.                                 *)
(* This is more like NNF than Mizar's version.                               *)
(* ------------------------------------------------------------------------- *)

let CORRELATE_RULE =
  PURE_REWRITE_RULE
   [TAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`;
    TAUT `(a ==> b) <=> ~a \/ b`;
    DE_MORGAN_THM;
    TAUT `~(~a) <=> a`;
    TAUT `~T <=> F`;
    TAUT `~F <=> T`;
    TAUT `T /\ p <=> p`;
    TAUT `p /\ T <=> p`;
    TAUT `F /\ p <=> F`;
    TAUT `p /\ F <=> F`;
    TAUT `T \/ p <=> T`;
    TAUT `p \/ T <=> T`;
    TAUT `F \/ p <=> p`;
    TAUT `p \/ F <=> p`;
    GSYM CONJ_ASSOC; GSYM DISJ_ASSOC;
    prove(`(?x. P x) <=> ~(!x. ~(P x))`,MESON_TAC[])];;

(* ------------------------------------------------------------------------- *)
(* Look for an immediate contradictory pair of theorems. This is quadratic,  *)
(* but I doubt if that's much of an issue in practice. We could do something *)
(* fancier, but need to be careful over alpha-equivalence if sorting.        *)
(* ------------------------------------------------------------------------- *)

let THMLIST_CONTR_RULE =
  let CONTR_PAIR_THM = UNDISCH_ALL(TAUT `p ==> ~p ==> F`)
  and p_tm = `p:bool` in
  fun ths ->
    let ths_n,ths_p = partition (is_neg o concl) ths in
    let th_n = find (fun thn -> let tm = rand(concl thn) in
                                exists (aconv tm o concl) ths_p) ths_n in
    let tm = rand(concl th_n) in
    let th_p = find (aconv tm o concl) ths_p in
    itlist PROVE_HYP [th_p; th_n] (INST [tm,p_tm] CONTR_PAIR_THM);;

(* ------------------------------------------------------------------------- *)
(* Hence something similar to Mizar's "prechecker".                          *)
(* ------------------------------------------------------------------------- *)

let PRECHECKER_THEN prover =
  SPLIT_THEN (fun ths -> try THMLIST_CONTR_RULE ths
                         with Failure _ ->
                             SPLIT_FOL_THEN prover (map CORRELATE_RULE ths));;

(* ------------------------------------------------------------------------- *)
(* Lazy equations for use in congruence closure.                             *)
(* ------------------------------------------------------------------------- *)

type lazyeq = Lazy of (term * term) * (unit -> thm);;

let cache f =
  let store = ref TRUTH in
  fun () -> let th = !store in
            if is_eq(concl th) then th else
            let th' = f() in
            (store := th'; th');;

let lazy_eq th =
  Lazy((dest_eq(concl th)),(fun () -> th));;

let lazy_eval (Lazy(_,f)) = f();;

let REFL' t = Lazy((t,t),cache(fun () -> REFL t));;

let SYM' = fun (Lazy((t,t'),f)) -> Lazy((t',t),cache(fun () -> SYM(f ())));;

let TRANS' =
  fun (Lazy((s,s'),f)) (Lazy((t,t'),g)) ->
     if not(aconv s' t) then failwith "TRANS'"
     else Lazy((s,t'),cache(fun () -> TRANS (f ()) (g ())));;

let MK_COMB' =
  fun (Lazy((s,s'),f),Lazy((t,t'),g)) ->
     Lazy((mk_comb(s,t),mk_comb(s',t')),cache(fun () -> MK_COMB (f (),g ())));;

let concl' = fun (Lazy(tmp,g)) -> tmp;;

(* ------------------------------------------------------------------------- *)
(* Successors of a term, and predecessor function.                           *)
(* ------------------------------------------------------------------------- *)

let successors tm =
  try let f,x = dest_comb tm in [f;x]
  with Failure _ -> [];;

let predecessor_function tms =
  itlist (fun x -> itlist (fun y f -> (y |-> insert x (tryapplyd f y [])) f)
                          (successors x))
         tms undefined;;

(* ------------------------------------------------------------------------- *)
(* A union-find structure for equivalences, with theorems for edges.         *)
(* ------------------------------------------------------------------------- *)

type termnode = Nonterminal of lazyeq | Terminal of term * term list;;

type termequivalence = Equivalence of (term,termnode)func;;

let rec terminus (Equivalence f as eqv) a =
  match (apply f a) with
    Nonterminal(th) -> let b = snd(concl' th) in
                       let th',n = terminus eqv b in
                       TRANS' th th',n
  | Terminal(t,n) -> (REFL' t,n);;

let tryterminus eqv a =
  try terminus eqv a with Failure _ -> (REFL' a,[a]);;

let canonize eqv a = fst(tryterminus eqv a);;

let equate th (Equivalence f as eqv) =
  let a,b = concl' th in
  let (ath,na) = tryterminus eqv a
  and (bth,nb) = tryterminus eqv b in
  let a' = snd(concl' ath) and b' = snd(concl' bth) in
  Equivalence
   (if a' = b' then f else
    if length na <= length nb then
      let th' = TRANS' (TRANS' (SYM' ath) th) bth in
      (a' |-> Nonterminal th') ((b' |-> Terminal(b',na@nb)) f)
    else
      let th' = TRANS'(SYM'(TRANS' th bth)) ath in
      (b' |-> Nonterminal th') ((a' |-> Terminal(a',na@nb)) f));;

let unequal = Equivalence undefined;;

let equated (Equivalence f) = dom f;;

let prove_equal eqv (s,t) =
  let sth = canonize eqv s and tth = canonize eqv t in
  TRANS' (canonize eqv s) (SYM'(canonize eqv t));;

let equivalence_class eqv a = snd(tryterminus eqv a);;

(* ------------------------------------------------------------------------- *)
(* Prove composite terms equivalent based on 1-step congruence.              *)
(* ------------------------------------------------------------------------- *)

let provecongruent eqv (tm1,tm2) =
  let f1,x1 = dest_comb tm1
  and f2,x2 = dest_comb tm2 in
  MK_COMB'(prove_equal eqv (f1,f2),prove_equal eqv (x1,x2));;

(* ------------------------------------------------------------------------- *)
(* Merge equivalence classes given equation "th", using congruence closure.  *)
(* ------------------------------------------------------------------------- *)

let rec emerge th (eqv,pfn) =
  let s,t = concl' th in
  let sth = canonize eqv s and tth = canonize eqv t in
  let s' = snd(concl' sth) and t' = snd(concl' tth) in
  if s' = t' then (eqv,pfn) else
  let sp = tryapplyd pfn s' [] and tp = tryapplyd pfn t' [] in
  let eqv' = equate th eqv in
  let stth = canonize eqv' s' in
  let sttm = snd(concl' stth) in
  let pfn' = (sttm |-> union sp tp) pfn in
  itlist (fun (u,v) (eqv,pfn as eqp) ->
             try let thuv = provecongruent eqv (u,v) in emerge thuv eqp
             with Failure _ -> eqp)
         (allpairs (fun u v -> (u,v)) sp tp) (eqv',pfn');;

(* ------------------------------------------------------------------------- *)
(* Find subterms of "tm" that contain as a subterm one of the "tms" terms.   *)
(* This is intended to be more efficient than the obvious "find_terms ...".  *)
(* ------------------------------------------------------------------------- *)

let rec supersubterms tms tm =
  let ltms,tms' =
    if mem tm tms then [tm],filter (fun t -> t <> tm) tms
    else [],tms in
  if tms' = [] then ltms else
  let stms =
    try let l,r = dest_comb tm in
    union (supersubterms tms' l) (supersubterms tms' r)
    with Failure _ -> [] in
  if stms = [] then ltms
  else tm::stms;;

(* ------------------------------------------------------------------------- *)
(* Find an appropriate term universe for overall terms "tms".                *)
(* ------------------------------------------------------------------------- *)

let term_universe tms =
  setify (itlist ((@) o supersubterms tms) tms []);;

(* ------------------------------------------------------------------------- *)
(* Congruence closure of "eqs" over term universe "tms".                     *)
(* ------------------------------------------------------------------------- *)

let congruence_closure tms eqs =
  let pfn = predecessor_function tms in
  let eqv,_ = itlist emerge eqs (unequal,pfn) in
  eqv;;

(* ------------------------------------------------------------------------- *)
(* Prove that "eq" follows from "eqs" by congruence closure.                 *)
(* ------------------------------------------------------------------------- *)

let CCPROVE eqs eq =
  let tps = dest_eq eq :: map concl' eqs in
  let otms = itlist (fun (x,y) l -> x::y::l) tps [] in
  let tms = term_universe(setify otms) in
  let eqv = congruence_closure tms eqs in
  prove_equal eqv (dest_eq eq);;

(* ------------------------------------------------------------------------- *)
(* Inference rule for `eq1 /\ ... /\ eqn ==> eq`                             *)
(* ------------------------------------------------------------------------- *)

let CONGRUENCE_CLOSURE tm =
  if is_imp tm then
    let eqs,eq = dest_imp tm in
    DISCH eqs (lazy_eval(CCPROVE (map lazy_eq (CONJUNCTS(ASSUME eqs))) eq))
  else lazy_eval(CCPROVE [] tm);;

(* ------------------------------------------------------------------------- *)
(* Inference rule for contradictoriness of set of +ve and -ve eqns.          *)
(* ------------------------------------------------------------------------- *)

let CONGRUENCE_CLOSURE_CONTR ths =
  let nths,pths = partition (is_neg o concl) ths in
  let peqs = filter (is_eq o concl) pths
  and neqs = filter (is_eq o rand o concl) nths in
  let tps = map (dest_eq o concl) peqs @ map (dest_eq o rand o concl) neqs in
  let otms = itlist (fun (x,y) l -> x::y::l) tps [] in
  let tms = term_universe(setify otms) in
  let eqv = congruence_closure tms (map lazy_eq peqs) in
  let prover th =
    let eq = dest_eq(rand(concl th)) in
    let lth = prove_equal eqv eq in
    EQ_MP (EQF_INTRO th) (lazy_eval lth) in
  tryfind prover neqs;;

(* ------------------------------------------------------------------------- *)
(* Attempt to prove equality between terms/formulas based on equivalence.    *)
(* Note that ABS sideconditions are only checked at inference-time...        *)
(* ------------------------------------------------------------------------- *)

let ABS' v =
  fun (Lazy((s,t),f)) ->
        Lazy((mk_abs(v,s),mk_abs(v,t)),
        cache(fun () -> ABS v (f ())));;

let ALPHA_EQ' s' t' =
  fun (Lazy((s,t),f) as inp) ->
        if s' = s && t' = t then inp else
        Lazy((s',t'),
             cache(fun () -> EQ_MP (ALPHA (mk_eq(s,t)) (mk_eq(s',t')))
                                   (f ())));;

let rec PROVE_EQUAL eqv (tm1,tm2 as tmp) =
  if tm1 = tm2 then REFL' tm1 else
  try prove_equal eqv tmp with Failure _ ->
  if is_comb tm1 && is_comb tm2 then
    let f1,x1 = dest_comb tm1
    and f2,x2 = dest_comb tm2 in
    MK_COMB'(PROVE_EQUAL eqv (f1,f2),PROVE_EQUAL eqv (x1,x2))
  else if is_abs tm1 && is_abs tm2 then
    let x1,bod1 = dest_abs tm1
    and x2,bod2 = dest_abs tm2 in
    let gv = genvar(type_of x1) in
    ALPHA_EQ' tm1 tm2
    (ABS' x1 (PROVE_EQUAL eqv (vsubst[gv,x1] bod1,vsubst[gv,x2] bod2)))
  else failwith "PROVE_EQUAL";;

let PROVE_EQUIVALENT eqv tm1 tm2 = lazy_eval (PROVE_EQUAL eqv (tm1,tm2));;

(* ------------------------------------------------------------------------- *)
(* Complementary version for formulas.                                       *)
(* ------------------------------------------------------------------------- *)

let PROVE_COMPLEMENTARY eqv th1 th2 =
  let tm1 = concl th1 and tm2 = concl th2 in
  if is_neg tm1 then
    let th = PROVE_EQUIVALENT eqv (rand tm1) tm2 in
    EQ_MP (EQF_INTRO th1) (EQ_MP (SYM th) th2)
  else if is_neg tm2 then
    let th = PROVE_EQUIVALENT eqv (rand tm2) tm1 in
    EQ_MP (EQF_INTRO th2) (EQ_MP (SYM th) th1)
  else failwith "PROVE_COMPLEMENTARY";;

(* ------------------------------------------------------------------------- *)
(* Check equality under equivalence with "env" mapping for first term.       *)
(* ------------------------------------------------------------------------- *)

let rec test_eq eqv (tm1,tm2) env =
  if is_comb tm1 && is_comb tm2 then
    let f1,x1 = dest_comb tm1
    and f2,x2 = dest_comb tm2 in
    test_eq eqv (f1,f2) env && test_eq eqv (x1,x2) env
  else if is_abs tm1 && is_abs tm2 then
    let x1,bod1 = dest_abs tm1
    and x2,bod2 = dest_abs tm2 in
    let gv = genvar(type_of x1) in
    test_eq eqv (vsubst[gv,x1] bod1,vsubst[gv,x2] bod2) env
  else if is_var tm1 && can (rev_assoc tm1) env then
    test_eq eqv (rev_assoc tm1 env,tm2) []
  else can (prove_equal eqv) (tm1,tm2);;

(* ------------------------------------------------------------------------- *)
(* Map a term to its equivalence class modulo equivalence                    *)
(* ------------------------------------------------------------------------- *)

let rec term_equivs eqv tm =
  let l = equivalence_class eqv tm in
  if l <> [tm] then l
  else if is_comb tm then
    let f,x = dest_comb tm in
    allpairs (curry mk_comb) (term_equivs eqv f) (term_equivs eqv x)
  else if is_abs tm then
    let v,bod = dest_abs tm in
    let gv = genvar(type_of v) in
    map (fun t -> alpha v (mk_abs(gv,t))) (term_equivs eqv (vsubst [gv,v] bod))
  else [tm];;

(* ------------------------------------------------------------------------- *)
(* Replace "outer" universal variables with genvars. This is "outer" in the  *)
(* second sense, i.e. universals not in scope of an existential or negation. *)
(* ------------------------------------------------------------------------- *)

let rec GENSPEC th =
  let tm = concl th in
  if is_forall tm then
    let v = bndvar(rand tm) in
    let gv = genvar(type_of v) in
    GENSPEC(SPEC gv th)
  else if is_conj tm then
    let th1,th2 = CONJ_PAIR th in
    CONJ (GENSPEC th1) (GENSPEC th2)
  else if is_disj tm then
    let th1 = GENSPEC(ASSUME(lhand tm))
    and th2 = GENSPEC(ASSUME(rand tm)) in
    let th3 = DISJ1 th1 (concl th2)
    and th4 = DISJ2 (concl th1) th2 in
    DISJ_CASES th th3 th4
  else th;;

(* ------------------------------------------------------------------------- *)
(* Simple first-order matching.                                              *)
(* ------------------------------------------------------------------------- *)

let rec term_fmatch vars vtm ctm env =
  if mem vtm vars then
    if can (rev_assoc vtm) env then
      term_fmatch vars (rev_assoc vtm env) ctm env
    else if aconv vtm ctm then env else (ctm,vtm)::env
  else if is_comb vtm && is_comb ctm then
    let fv,xv = dest_comb vtm
    and fc,xc = dest_comb ctm in
    term_fmatch vars fv fc (term_fmatch vars xv xc env)
  else if is_abs vtm && is_abs ctm then
    let xv,bodv = dest_abs vtm
    and xc,bodc = dest_abs ctm in
    let gv = genvar(type_of xv) and gc = genvar(type_of xc) in
    let gbodv = vsubst [gv,xv] bodv
    and gbodc = vsubst [gc,xc] bodc in
    term_fmatch (gv::vars) gbodv gbodc ((gc,gv)::env)
  else if vtm = ctm then env
  else failwith "term_fmatch";;

let rec check_consistency env =
  match env with
    [] -> true
  | (c,v)::es -> forall (fun (c',v') -> v' <> v || c' = c) es;;

let separate_insts env =
  let tyin = itlist (fun (c,v) -> type_match (type_of v) (type_of c))
                    env [] in
  let ifn(c,v) = (inst tyin c,inst tyin v) in
  let tmin = setify (map ifn env) in
  if check_consistency tmin then (tmin,tyin)
  else failwith "separate_insts";;

let first_order_match vars vtm ctm env =
  let env' = term_fmatch vars vtm ctm env in
  if can separate_insts env' then env' else failwith "first_order_match";;

(* ------------------------------------------------------------------------- *)
(* Try to match all leaves to negation of auxiliary propositions.            *)
(* ------------------------------------------------------------------------- *)

let matchleaves =
  let rec matchleaves vars vtm ctms env cont =
    if is_conj vtm then
      try matchleaves vars (rand vtm) ctms env cont
      with Failure _ -> matchleaves vars (lhand vtm) ctms env cont
    else if is_disj vtm then
      matchleaves vars (lhand vtm) ctms env
       (fun e -> matchleaves vars (rand vtm) ctms e cont)
    else
      tryfind (fun ctm -> cont (first_order_match vars vtm ctm env)) ctms in
  fun vars vtm ctms env -> matchleaves vars vtm ctms env (fun e -> e);;

(* ------------------------------------------------------------------------- *)
(* Now actually do the refutation once theorem is instantiated.              *)
(* ------------------------------------------------------------------------- *)

let rec REFUTE_LEAVES eqv cths th =
  let tm = concl th in
  if is_conj tm then
    try REFUTE_LEAVES eqv cths (CONJUNCT1 th)
    with Failure _ -> REFUTE_LEAVES eqv cths (CONJUNCT2 th)
  else if is_disj tm then
    let th1 = REFUTE_LEAVES eqv cths (ASSUME(lhand tm))
    and th2 = REFUTE_LEAVES eqv cths (ASSUME(rand tm)) in
    DISJ_CASES th th1 th2
  else
    tryfind (PROVE_COMPLEMENTARY eqv th) cths;;

(* ------------------------------------------------------------------------- *)
(* Hence the Mizar "unifier" for given universal formula.                    *)
(* ------------------------------------------------------------------------- *)

let negate tm = if is_neg tm then rand tm else mk_neg tm;;

let MIZAR_UNIFIER eqv ths th =
  let gth = GENSPEC th in
  let vtm = concl gth in
  let vars = subtract (frees vtm) (frees(concl th))
  and ctms = map (negate o concl) ths in
  let allctms = itlist (union o term_equivs eqv) ctms [] in
  let env = matchleaves vars vtm allctms [] in
  let tmin,tyin = separate_insts env in
  REFUTE_LEAVES eqv ths (PINST tyin tmin gth);;

(* ------------------------------------------------------------------------- *)
(* Deduce disequalities of subterms and add symmetric versions at the end.   *)
(* ------------------------------------------------------------------------- *)

let rec DISEQUALITIES ths =
  match ths with
    [] -> []
  | th::oths ->
        let t1,t2 = dest_eq (rand(concl th)) in
        let f1,args1 = strip_comb t1
        and f2,args2 = strip_comb t2 in
        if f1 <> f2 || length args1 <> length args2
        then th::(GSYM th)::(DISEQUALITIES oths) else
        let zargs = zip args1 args2 in
        let diffs = filter (fun (a1,a2) -> a1 <> a2) zargs in
        if length diffs <> 1 then th::(GSYM th)::(DISEQUALITIES oths) else
        let eths = map (fun (a1,a2) ->
          if a1 = a2 then REFL a1 else ASSUME(mk_eq(a1,a2))) zargs in
        let th1 = rev_itlist (fun x y -> MK_COMB(y,x)) eths (REFL f1) in
        let th2 =
          MP (GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM] (DISCH_ALL th1)) th in
        th::(GSYM th)::(DISEQUALITIES(th2::oths));;

(* ------------------------------------------------------------------------- *)
(* Get such a starting inequality from complementary literals.               *)
(* ------------------------------------------------------------------------- *)

let ATOMINEQUALITIES th1 th2 =
  let t1 = concl th1 and t2' = concl th2 in
  let t2 = dest_neg t2' in
  let f1,args1 = strip_comb t1
  and f2,args2 = strip_comb t2 in
  if f1 <> f2 || length args1 <> length args2 then [] else
  let zargs = zip args1 args2 in
  let diffs = filter (fun (a1,a2) -> a1 <> a2) zargs in
  if length diffs <> 1 then [] else
  let eths = map (fun (a1,a2) ->
    if a1 = a2 then REFL a1 else ASSUME(mk_eq(a1,a2))) zargs in
  let th3 = rev_itlist (fun x y -> MK_COMB(y,x)) eths (REFL f1) in
  let th4 = EQ_MP (TRANS th3 (EQF_INTRO th2)) th1 in
  let th5 = NOT_INTRO(itlist (DISCH o mk_eq) diffs th4) in
  [itlist PROVE_HYP [th1; th2] th5];;

(* ------------------------------------------------------------------------- *)
(* Basic prover.                                                             *)
(* ------------------------------------------------------------------------- *)

let BASIC_MIZARBY ths =
  try let nths,pths = partition (is_neg o concl) ths in
      let peqs,pneqs = partition (is_eq o concl) pths
      and neqs,nneqs = partition (is_eq o rand o concl) nths in
      let tps = map (dest_eq o concl) peqs @
                map (dest_eq o rand o concl) neqs in
      let otms = itlist (fun (x,y) l -> x::y::l) tps [] in
      let tms = term_universe(setify otms) in
      let eqv = congruence_closure tms (map lazy_eq peqs) in
      let eqprover th =
        let s,t = dest_eq(rand(concl th)) in
        let th' = PROVE_EQUIVALENT eqv s t in
        EQ_MP (EQF_INTRO th) th'
      and contrprover thp thn =
        let th = PROVE_EQUIVALENT eqv (concl thp) (rand(concl thn)) in
        EQ_MP (TRANS th (EQF_INTRO thn)) thp in
      try tryfind eqprover neqs with Failure _ ->
      try tryfind (fun thp -> tryfind (contrprover thp) nneqs) pneqs
      with Failure _ ->
        let new_neqs = unions(allpairs ATOMINEQUALITIES pneqs nneqs) in
        let allths = pneqs @ nneqs @ peqs @ DISEQUALITIES(neqs @ new_neqs) in
        tryfind (MIZAR_UNIFIER eqv allths)
                (filter (is_forall o concl) allths)
   with Failure _ -> failwith "BASIC_MIZARBY";;

(* ------------------------------------------------------------------------- *)
(* Put it all together.                                                      *)
(* ------------------------------------------------------------------------- *)

let MIZAR_REFUTER ths = PRECHECKER_THEN BASIC_MIZARBY ths;;

(* ------------------------------------------------------------------------- *)
(* The Mizar prover for getting a conclusion from hypotheses.                *)
(* ------------------------------------------------------------------------- *)

let MIZAR_BY =
  let pth = TAUT `(~p ==> F) <=> p` and p_tm = `p:bool` in
  fun ths tm ->
    let tm' = mk_neg tm in
    let th0 = ASSUME tm' in
    let th1 = MIZAR_REFUTER (th0::ths) in
    EQ_MP (INST [tm,p_tm] pth) (DISCH tm' th1);;

(* ------------------------------------------------------------------------- *)
(* As a standalone prover of formulas.                                       *)
(* ------------------------------------------------------------------------- *)

let MIZAR_RULE tm = MIZAR_BY [] tm;;

(* ------------------------------------------------------------------------- *)
(* Some additional stuff for HOL.                                            *)
(* ------------------------------------------------------------------------- *)

let HOL_BY =
  let BETASET_CONV =
    TOP_DEPTH_CONV GEN_BETA_CONV THENC REWRITE_CONV[IN_ELIM_THM]
  and BUILTIN_CONV tm =
    try EQT_ELIM(NUM_REDUCE_CONV tm) with Failure _ ->
    try EQT_ELIM(REAL_RAT_REDUCE_CONV tm) with Failure _ ->
    try ARITH_RULE tm with Failure _ ->
    try REAL_ARITH tm with Failure _ ->
    failwith "BUILTIN_CONV" in
  fun ths tm ->
    try MIZAR_BY ths tm with Failure _ ->
    try tryfind (fun th -> PART_MATCH I th tm) ths with Failure _ ->
    try let avs,bod = strip_forall tm in
        let gvs = map (genvar o type_of) avs in
        let gtm = vsubst (zip gvs avs) bod in
        let th = tryfind (fun th -> PART_MATCH I th gtm) ths in
        let gth = GENL gvs th in
        EQ_MP (ALPHA (concl gth) tm) gth
    with Failure _ -> try
       (let ths' = map BETA_RULE ths
        and th' = TOP_DEPTH_CONV BETA_CONV tm in
        let tm' = rand(concl th') in
        try EQ_MP (SYM th') (tryfind (fun th -> PART_MATCH I th tm') ths)
        with Failure _ -> try EQ_MP (SYM th') (BUILTIN_CONV tm')
        with Failure _ ->
          let ths'' = map (CONV_RULE BETASET_CONV) ths'
          and th'' = TRANS th' (BETASET_CONV tm') in
          EQ_MP (SYM th'') (prove(rand(concl th''),MESON_TAC ths'')))
    with Failure _ -> failwith "HOL_BY";;

(* ------------------------------------------------------------------------- *)
(* Standalone prover, breaking down an implication first.                    *)
(* ------------------------------------------------------------------------- *)

let HOL_RULE tm =
  try let l,r = dest_imp tm in
      DISCH l (HOL_BY (CONJUNCTS(ASSUME l)) r)
  with Failure _ -> HOL_BY [] tm;;

(* ------------------------------------------------------------------------- *)
(* Tautology examples (Pelletier problems).                                  *)
(* ------------------------------------------------------------------------- *)

let prop_1 = time HOL_RULE
 `p ==> q <=> ~q ==> ~p`;;

let prop_2 = time HOL_RULE
 `~ ~p <=> p`;;

let prop_3 = time HOL_RULE
 `~(p ==> q) ==> q ==> p`;;

let prop_4 = time HOL_RULE
 `~p ==> q <=> ~q ==> p`;;

let prop_5 = time HOL_RULE
 `(p \/ q ==> p \/ r) ==> p \/ (q ==> r)`;;

let prop_6 = time HOL_RULE
 `p \/ ~p`;;

let prop_7 = time HOL_RULE
 `p \/ ~ ~ ~p`;;

let prop_8 = time HOL_RULE
 `((p ==> q) ==> p) ==> p`;;

let prop_9 = time HOL_RULE
 `(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)`;;

let prop_10 = time HOL_RULE
 `(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)`;;

let prop_11 = time HOL_RULE
 `p <=> p`;;

let prop_12 = time HOL_RULE
 `((p <=> q) <=> r) <=> (p <=> (q <=> r))`;;

let prop_13 = time HOL_RULE
 `p \/ q /\ r <=> (p \/ q) /\ (p \/ r)`;;

let prop_14 = time HOL_RULE
 `(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)`;;

let prop_15 = time HOL_RULE
 `p ==> q <=> ~p \/ q`;;

let prop_16 = time HOL_RULE
 `(p ==> q) \/ (q ==> p)`;;

let prop_17 = time HOL_RULE
 `p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)`;;

(* ------------------------------------------------------------------------- *)
(* Congruence closure examples.                                              *)
(* ------------------------------------------------------------------------- *)

time HOL_RULE
 `(f(f(f(f(f(x))))) = x) /\ (f(f(f(x))) = x) ==> (f(x) = x)`;;

time HOL_RULE
 `(f(f(f(f(f(f(x)))))) = x) /\ (f(f(f(f(x)))) = x) ==> (f(f(x)) = x)`;;

time HOL_RULE `(f a = a) ==> (f(f a) = a)`;;

time HOL_RULE
  `(a = f a) /\ ((g b (f a))=(f (f a))) /\ ((g a b)=(f (g b a)))
   ==> (g a b = a)`;;

time HOL_RULE
  `((s(s(s(s(s(s(s(s(s(s(s(s(s(s(s a)))))))))))))))=a) /\
   ((s (s (s (s (s (s (s (s (s (s a))))))))))=a) /\
   ((s (s (s (s (s (s a))))))=a)
   ==> (a = s a)`;;

time HOL_RULE `(u = v) ==> (P u <=> P v)`;;

time HOL_RULE
  `(b + c + d + e + f + g + h + i + j + k + l + m =
    m + l + k + j + i + h + g + f + e + d + c + b)
   ==> (a + b + c + d + e + f + g + h + i + j + k + l + m =
        a + m + l + k + j + i + h + g + f + e + d + c + b)`;;

time HOL_RULE
  `(f(f(f(f(a)))) = a) /\ (f(f(f(f(f(f(a)))))) = a) /\
   something(irrelevant) /\ (11 + 12 = 23) /\
   (f(f(f(f(b)))) = f(f(f(f(f(f(f(f(f(f(c))))))))))) /\
   ~(otherthing) /\ ~(f(a) = a) /\ ~(f(b) = b) /\
   P(f(f(f(a)))) ==> P(f(a))`;;

time HOL_RULE
  `((a = b) \/ (c = d)) /\ ((a = c) \/ (b = d)) ==> (a = d) \/ (b = c)`;;

(* ------------------------------------------------------------------------- *)
(* Various combined examples.                                                *)
(* ------------------------------------------------------------------------- *)

time HOL_RULE
  `(f(f(f(f(a:A)))) = a) /\ (f(f(f(f(f(f(a)))))) = a) /\
   something(irrelevant) /\ (11 + 12 = 23) /\
   (f(f(f(f(b:A)))) = f(f(f(f(f(f(f(f(f(f(c))))))))))) /\
   ~(otherthing) /\ ~(f(a) = a) /\ ~(f(b) = b) /\
   P(f(a)) /\ ~(f(f(f(a))) = f(a)) ==> ?x. P(f(f(f(x))))`;;

time HOL_RULE
  `(f(f(f(f(a:A)))) = a) /\ (f(f(f(f(f(f(a)))))) = a) /\
   something(irrelevant) /\ (11 + 12 = 23) /\
   (f(f(f(f(b:A)))) = f(f(f(f(f(f(f(f(f(f(c))))))))))) /\
   ~(otherthing) /\ ~(f(a) = a) /\ ~(f(b) = b) /\
   P(f(a))
   ==> P(f(f(f(a))))`;;

time HOL_RULE
  `(f(f(f(f(a:A)))) = a) /\ (f(f(f(f(f(f(a)))))) = a) /\
   something(irrelevant) /\ (11 + 12 = 23) /\
   (f(f(f(f(b:A)))) = f(f(f(f(f(f(f(f(f(f(c))))))))))) /\
   ~(otherthing) /\ ~(f(a) = a) /\ ~(f(b) = b) /\
   P(f(a))
   ==> ?x. P(f(f(f(x))))`;;

time HOL_RULE
  `(a = f a) /\ ((g b (f a))=(f (f a))) /\ ((g a b)=(f (g b a))) /\
   (!x y. ~P (g x y))
   ==> ~P(a)`;;

time HOL_RULE
 `(!x y. x + y = y + x) /\ (1 + 2 = x) /\ (x = 3) ==> (3 = 2 + 1)`;;

time HOL_RULE
 `(!x:num y. x + y = y + x) ==> (1 + 2 = 2 + 1)`;;

time HOL_RULE
 `(!x:num y. ~(x + y = y + x)) ==> ~(1 + 2 = 2 + 1)`;;

time HOL_RULE
 `(1 + 2 = 2 + 1) ==> ?x:num y. x + y = y + x`;;

time HOL_RULE
 `(1 + x = x + 1) ==> ?x:num y. x + y = y + x`;;

time (HOL_BY []) `?x. P x ==> !y. P y`;;

(* ------------------------------------------------------------------------- *)
(* Testing the HOL extensions.                                               *)
(* ------------------------------------------------------------------------- *)

time HOL_RULE `1 + 1 = 2`;;

time HOL_RULE `(\x. x + 1) 2 = 2 + 1`;;

time HOL_RULE `!x. x < 2 ==> 2 * x <= 3`;;

time HOL_RULE `y IN {x | x < 2} <=> y < 2`;;

time HOL_RULE `(!x. (x = a) \/ x > a) ==> (1 + x = a) \/ 1 + x > a`;;

time HOL_RULE `(\(x,y). x + y)(1,2) + 5 = (1 + 2) + 5`;;

(* ------------------------------------------------------------------------- *)
(* These and only these should go to MESON.                                  *)
(* ------------------------------------------------------------------------- *)

print_string "***** Now the following (only) should use MESON";
print_newline();;

time HOL_RULE `?x y. x = y`;;

time HOL_RULE `(!Y X Z. p(X,Y) /\ p(Y,Z) ==> p(X,Z)) /\
               (!Y X Z. q(X,Y) /\ q(Y,Z) ==> q(X,Z)) /\
               (!Y X. q(X,Y) ==> q(Y,X)) /\
               (!X Y. p(X,Y) \/ q(X,Y))
               ==> p(a,b) \/ q(c,d)`;;

time HOL_BY [PAIR_EQ] `(1,2) IN {(x,y) | x < y} <=> 1 < 2`;;

HOL_BY [] `?x. !y. P x ==> P y`;;
