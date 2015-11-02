(* ========================================================================= *)
(* Formalization of general topological and metric spaces in HOL Light       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*                (c) Copyright, Marco Maggesi 2014                          *)
(* ========================================================================= *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Instrument classical tactics to attach label to inductive hypothesis.     *)
(* ------------------------------------------------------------------------- *)

let LABEL_INDUCT_TAC =
  let IND_TAC = MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC in
  fun (asl,w as gl) ->
    let s = fst (dest_var (fst (dest_forall w)))  in
    (IND_TAC THENL
     [ALL_TAC; GEN_TAC THEN DISCH_THEN (LABEL_TAC("ind_"^s))])
    gl;;

let LABEL_ABBREV_TAC tm =
  let cvs,t = dest_eq tm in
  let v,vs = strip_comb cvs in
  let s = name_of v in
  let rs = list_mk_abs(vs,t) in
  let eq = mk_eq(rs,v) in
  let th1 = itlist (fun v th -> CONV_RULE(LAND_CONV BETA_CONV) (AP_THM th v))
                   (rev vs) (ASSUME eq) in
  let th2 = SIMPLE_CHOOSE v (SIMPLE_EXISTS v (GENL vs th1)) in
  let th3 = PROVE_HYP (EXISTS(mk_exists(v,eq),rs) (REFL rs)) th2 in
  fun (asl,w as gl) ->
    let avoids = itlist (union o frees o concl o snd) asl (frees w) in
    if mem v avoids then failwith "LABEL_ABBREV_TAC: variable already used" else
    CHOOSE_THEN
     (fun th -> RULE_ASSUM_TAC(PURE_ONCE_REWRITE_RULE[th]) THEN
                PURE_ONCE_REWRITE_TAC[th] THEN
                LABEL_TAC s th)
     th3 gl;;

(* ------------------------------------------------------------------------- *)
(* Further tactics for structuring the proof flow.                           *)
(* ------------------------------------------------------------------------- *)

let CUT_TAC : term -> tactic =
  let th = MESON [] `(p ==> q) /\ p ==> q`
  and ptm = `p:bool` in
  fun tm -> MATCH_MP_TAC (INST [tm,ptm] th) THEN CONJ_TAC;;

let CLAIM_TAC s tm = SUBGOAL_THEN tm (DESTRUCT_TAC s);;

let CONJ_LIST = end_itlist CONJ;;

(* ------------------------------------------------------------------------- *)
(* General notion of a topology.                                             *)
(* ------------------------------------------------------------------------- *)

let istopology = new_definition
 `istopology L <=>
        {} IN L /\
        (!s t. s IN L /\ t IN L ==> (s INTER t) IN L) /\
        (!k. k SUBSET L ==> (UNIONS k) IN L)`;;

let topology_tybij_th = prove
 (`?t:(A->bool)->bool. istopology t`,
  EXISTS_TAC `UNIV:(A->bool)->bool` THEN REWRITE_TAC[istopology; IN_UNIV]);;

let topology_tybij =
  new_type_definition "topology" ("topology","open_in") topology_tybij_th;;

let ISTOPOLOGY_OPEN_IN = prove
 (`istopology(open_in top)`,
  MESON_TAC[topology_tybij]);;

let TOPOLOGY_EQ = prove
 (`!top1 top2. top1 = top2 <=> !s. open_in top1 s <=> open_in top2 s`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[ETA_AX] THEN MESON_TAC[topology_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Infer the "universe" from union of all sets in the topology.              *)
(* ------------------------------------------------------------------------- *)

let topspace = new_definition
 `topspace top = UNIONS {s | open_in top s}`;;

(* ------------------------------------------------------------------------- *)
(* Main properties of open sets.                                             *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_CLAUSES = prove
 (`!top:(A)topology.
        open_in top {} /\
        (!s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)) /\
        (!k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k))`,
  SIMP_TAC[IN; SUBSET; SIMP_RULE[istopology; IN; SUBSET] ISTOPOLOGY_OPEN_IN]);;

let OPEN_IN_SUBSET = prove
 (`!top s. open_in top s ==> s SUBSET (topspace top)`,
  REWRITE_TAC[topspace] THEN SET_TAC[]);;

let OPEN_IN_EMPTY = prove
 (`!top. open_in top {}`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_INTER = prove
 (`!top s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_UNIONS = prove
 (`!top k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k)`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_UNION = prove
 (`!top s t. open_in top s /\ open_in top t ==> open_in top (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[]);;

let OPEN_IN_TOPSPACE = prove
 (`!top. open_in top (topspace top)`,
  SIMP_TAC[topspace; OPEN_IN_UNIONS; IN_ELIM_THM]);;

let OPEN_IN_INTERS = prove
 (`!top s:(A->bool)->bool.
        FINITE s /\ ~(s = {}) /\ (!t. t IN s ==> open_in top t)
        ==> open_in top (INTERS s)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT; IMP_IMP; NOT_INSERT_EMPTY; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_SIMP_TAC[INTERS_0; INTER_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[]);;

let OPEN_IN_SUBOPEN = prove
 (`!top s:A->bool.
        open_in top s <=>
        !x. x IN s ==> ?t. open_in top t /\ x IN t /\ t SUBSET s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[GSYM FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_UNIONS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let closed_in = new_definition
 `closed_in top s <=>
        s SUBSET (topspace top) /\ open_in top (topspace top DIFF s)`;;

let CLOSED_IN_SUBSET = prove
 (`!top s. closed_in top s ==> s SUBSET (topspace top)`,
  MESON_TAC[closed_in]);;

let CLOSED_IN_EMPTY = prove
 (`!top. closed_in top {}`,
  REWRITE_TAC[closed_in; EMPTY_SUBSET; DIFF_EMPTY; OPEN_IN_TOPSPACE]);;

let CLOSED_IN_TOPSPACE = prove
 (`!top. closed_in top (topspace top)`,
  REWRITE_TAC[closed_in; SUBSET_REFL; DIFF_EQ_EMPTY; OPEN_IN_EMPTY]);;

let CLOSED_IN_UNION = prove
 (`!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s UNION t)`,
  SIMP_TAC[closed_in; UNION_SUBSET; OPEN_IN_INTER;
           SET_RULE `u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)`]);;

let CLOSED_IN_INTERS = prove
 (`!top k:(A->bool)->bool.
        ~(k = {}) /\ (!s. s IN k ==> closed_in top s)
        ==> closed_in top (INTERS k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[closed_in] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace top DIFF INTERS k :A->bool =
                UNIONS {topspace top DIFF s | s IN k}` SUBST1_TAC
  THENL [ALL_TAC; MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[IN_UNIONS; IN_INTERS; IN_DIFF; EXISTS_IN_IMAGE] THEN
  MESON_TAC[]);;

let CLOSED_IN_INTER = prove
 (`!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC CLOSED_IN_INTERS THEN ASM SET_TAC[]);;

let OPEN_IN_CLOSED_IN_EQ = prove
 (`!top s. open_in top s <=>
           s SUBSET topspace top /\ closed_in top (topspace top DIFF s)`,
  REWRITE_TAC[closed_in; SET_RULE `(u DIFF s) SUBSET u`] THEN
  REWRITE_TAC[SET_RULE `u DIFF (u DIFF s) = u INTER s`] THEN
  MESON_TAC[OPEN_IN_SUBSET; SET_RULE `s SUBSET t ==> t INTER s = s`]);;

let OPEN_IN_CLOSED_IN = prove
 (`!s. s SUBSET topspace top
       ==> (open_in top s <=> closed_in top (topspace top DIFF s))`,
  SIMP_TAC[OPEN_IN_CLOSED_IN_EQ]);;

let OPEN_IN_DIFF = prove
 (`!top s t:A->bool.
      open_in top s /\ closed_in top t ==> open_in top (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s DIFF t :A->bool = s INTER (topspace top DIFF t)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[closed_in]]);;

let CLOSED_IN_DIFF = prove
 (`!top s t:A->bool.
        closed_in top s /\ open_in top t ==> closed_in top (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s DIFF t :A->bool = s INTER (topspace top DIFF t)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_MESON_TAC[OPEN_IN_CLOSED_IN_EQ]]);;

let CLOSED_IN_UNIONS = prove
 (`!top s. FINITE s /\ (!t. t IN s ==> closed_in top t)
           ==> closed_in top (UNIONS s)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; CLOSED_IN_EMPTY; IN_INSERT] THEN
  MESON_TAC[CLOSED_IN_UNION]);;

let CLOSED_IN_LOCALLY_FINITE_UNIONS = prove                       
 (`!top f:(A->bool)->bool.                
        (!s. s IN f ==> closed_in top s) /\                          
        (!x. x IN topspace top                                               
             ==> ?v. open_in top v /\ x IN v /\                        
                     FINITE {s | s IN f /\ ~(s INTER v = {})}) 
        ==> closed_in top (UNIONS f)`,                   
  REPEAT STRIP_TAC THEN REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[closed_in]) THEN                             
     ASM_SIMP_TAC[UNIONS_SUBSET];
     ALL_TAC] THEN                      
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN              
  DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN EXISTS_TAC
    `v DIFF UNIONS {s | s IN f /\ ~(s INTER v = {})}:A->bool` THEN
  ASM_REWRITE_TAC[IN_DIFF; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL          
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_UNIONS THEN ASM_SIMP_TAC[IN_ELIM_THM]; 
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Subspace topology.                                                        *)
(* ------------------------------------------------------------------------- *)

let subtopology = new_definition
 `subtopology top u = topology {s INTER u | open_in top s}`;;

let ISTOPLOGY_SUBTOPOLOGY = prove
 (`!top u:A->bool. istopology {s INTER u | open_in top s}`,
  REWRITE_TAC[istopology; SET_RULE
   `{s INTER u | open_in top s} =
    IMAGE (\s. s INTER u) {s | open_in top s}`] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[SUBSET_IMAGE; IN_IMAGE; IN_ELIM_THM; SUBSET] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN REWRITE_TAC[OPEN_IN_EMPTY; INTER_EMPTY];
    SIMP_TAC[SET_RULE `(s INTER u) INTER t INTER u = (s INTER t) INTER u`] THEN
    ASM_MESON_TAC[OPEN_IN_INTER];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:(A->bool)->bool`; `g:(A->bool)->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `UNIONS g :A->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_UNIONS; INTER_UNIONS] THEN SET_TAC[]]);;

let OPEN_IN_SUBTOPOLOGY = prove
 (`!top u s. open_in (subtopology top u) s <=>
                ?t. open_in top t /\ s = t INTER u`,
  REWRITE_TAC[subtopology] THEN
  SIMP_TAC[REWRITE_RULE[CONJUNCT2 topology_tybij] ISTOPLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM]);;

let TOPSPACE_SUBTOPOLOGY = prove
 (`!top u. topspace(subtopology top u) = topspace top INTER u`,
  REWRITE_TAC[topspace; OPEN_IN_SUBTOPOLOGY; INTER_UNIONS] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM]);;

let CLOSED_IN_SUBTOPOLOGY = prove
 (`!top u s. closed_in (subtopology top u) s <=>
                ?t:A->bool. closed_in top t /\ s = t INTER u`,
  REWRITE_TAC[closed_in; TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET_INTER; OPEN_IN_SUBTOPOLOGY; RIGHT_AND_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `topspace top DIFF t :A->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_TOPSPACE; OPEN_IN_DIFF; CLOSED_IN_DIFF;
               OPEN_IN_TOPSPACE] THEN
  ASM SET_TAC[]);;

let OPEN_IN_SUBTOPOLOGY_EMPTY = prove
 (`!top s. open_in (subtopology top {}) s <=> s = {}`,
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; INTER_EMPTY] THEN
  MESON_TAC[OPEN_IN_EMPTY]);;

let CLOSED_IN_SUBTOPOLOGY_EMPTY = prove
 (`!top s. closed_in (subtopology top {}) s <=> s = {}`,
  REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY; INTER_EMPTY] THEN
  MESON_TAC[CLOSED_IN_EMPTY]);;

let OPEN_IN_SUBTOPOLOGY_REFL = prove
 (`!top u:A->bool. open_in (subtopology top u) u <=> u SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    DISCH_TAC THEN EXISTS_TAC `topspace top:A->bool` THEN
    REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM SET_TAC[]]);;

let CLOSED_IN_SUBTOPOLOGY_REFL = prove
 (`!top u:A->bool. closed_in (subtopology top u) u <=> u SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
    ASM_SIMP_TAC[CLOSED_IN_SUBSET];
    DISCH_TAC THEN EXISTS_TAC `topspace top:A->bool` THEN
    REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN ASM SET_TAC[]]);;

let SUBTOPOLOGY_SUPERSET = prove
 (`!top s:A->bool. topspace top SUBSET s ==> subtopology top s = top`,
  REPEAT GEN_TAC THEN SIMP_TAC[TOPOLOGY_EQ; OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_TAC THEN X_GEN_TAC `u:A->bool` THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN
      ASSUME_TAC(MATCH_MP OPEN_IN_SUBSET th)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN EXISTS_TAC `u:A->bool` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]]);;

let SUBTOPOLOGY_TOPSPACE = prove
 (`!top. subtopology top (topspace top) = top`,
  SIMP_TAC[SUBTOPOLOGY_SUPERSET; SUBSET_REFL]);;

let SUBTOPOLOGY_UNIV = prove
 (`!top. subtopology top UNIV = top`,
  SIMP_TAC[SUBTOPOLOGY_SUPERSET; SUBSET_UNIV]);;

let OPEN_IN_IMP_SUBSET = prove
 (`!top s t. open_in (subtopology top s) t ==> t SUBSET s`,
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN SET_TAC[]);;

let CLOSED_IN_IMP_SUBSET = prove
 (`!top s t. closed_in (subtopology top s) t ==> t SUBSET s`,
  REWRITE_TAC[closed_in; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

let OPEN_IN_SUBTOPOLOGY_UNION = prove
 (`!top s t u:A->bool.
        open_in (subtopology top t) s /\ open_in (subtopology top u) s
        ==> open_in (subtopology top (t UNION u)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s':A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t':A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s' INTER t':A->bool` THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN
  ASM SET_TAC[]);;

let CLOSED_IN_SUBTOPOLOGY_UNION = prove
 (`!top s t u:A->bool.
        closed_in (subtopology top t) s /\ closed_in (subtopology top u) s
        ==> closed_in (subtopology top (t UNION u)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s':A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t':A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s' INTER t':A->bool` THEN ASM_SIMP_TAC[CLOSED_IN_INTER] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A variant of nets (slightly non-standard but good for our purposes).      *)
(* ------------------------------------------------------------------------- *)

let net_tybij = new_type_definition "net" ("mk_net","netord")
 (prove
   (`?g:A->A->bool. !x y. (!z. g z x ==> g z y) \/ (!z. g z y ==> g z x)`,
    EXISTS_TAC `\x:A y:A. F` THEN REWRITE_TAC[]));;

let NET = prove
 (`!n x y. (!z. netord n z x ==> netord n z y) \/
           (!z. netord n z y ==> netord n z x)`,
   REWRITE_TAC[net_tybij; ETA_AX]);;

let OLDNET = prove
 (`!n x y. netord n x x /\ netord n y y
           ==> ?z. netord n z z /\
                   !w. netord n w z ==> netord n w x /\ netord n w y`,
  MESON_TAC[NET]);;

let NET_DILEMMA = prove
 (`!net. (?a. (?x. netord net x a) /\ (!x. netord net x a ==> P x)) /\
         (?b. (?x. netord net x b) /\ (!x. netord net x b ==> Q x))
         ==> ?c. (?x. netord net x c) /\ (!x. netord net x c ==> P x /\ Q x)`,
  MESON_TAC[NET]);;

(* ------------------------------------------------------------------------- *)
(* Sequential net and the "within" modifier for nets.                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("within",(14,"right"));;

let sequentially = new_definition
  `sequentially = mk_net(\m:num n. m >= n)`;;

let within = new_definition
  `net within s = mk_net(\x y. netord net x y /\ x IN s)`;;

let NET_PROVE_TAC[def] =
  REWRITE_TAC[GSYM FUN_EQ_THM; def] THEN
  REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[GSYM(CONJUNCT2 net_tybij)];;

let SEQUENTIALLY = prove
 (`!m n. netord sequentially m n <=> m >= n`,
  NET_PROVE_TAC[sequentially] THEN REWRITE_TAC[GE; LE_REFL] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let WITHIN = prove
 (`!n s x y. netord(n within s) x y <=> netord n x y /\ x IN s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[within; GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 net_tybij); ETA_AX] THEN
  MESON_TAC[NET]);;

let NET_WITHIN_UNIV = prove
 (`!net. net within UNIV = net`,
  REWRITE_TAC[within; IN_UNIV; ETA_AX; net_tybij]);;

let WITHIN_WITHIN = prove
 (`!net s t. (net within s) within t = net within (s INTER t)`,
  ONCE_REWRITE_TAC[within] THEN
  REWRITE_TAC[WITHIN; IN_INTER; GSYM CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Identify trivial limits, where we can't approach arbitrarily closely.     *)
(* ------------------------------------------------------------------------- *)

let trivial_limit = new_definition
  `trivial_limit net <=>
     (!a:A b. a = b) \/
     ?a:A b. ~(a = b) /\ !x. ~(netord(net) x a) /\ ~(netord(net) x b)`;;

let TRIVIAL_LIMIT_SEQUENTIALLY = prove
 (`~(trivial_limit sequentially)`,
  REWRITE_TAC[trivial_limit; SEQUENTIALLY] THEN
  MESON_TAC[GE_REFL; NOT_SUC]);;

let NONTRIVIAL_LIMIT_WITHIN = prove
 (`!net s. trivial_limit net ==> trivial_limit(net within s)`,
  REWRITE_TAC[trivial_limit; WITHIN] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some property holds "sufficiently close" to the limit point.              *)
(* ------------------------------------------------------------------------- *)

let eventually = new_definition
 `eventually p net <=>
        trivial_limit net \/
        ?y. (?x. netord net x y) /\ (!x. netord net x y ==> p x)`;;

let EVENTUALLY_HAPPENS = prove
 (`!net p. eventually p net ==> trivial_limit net \/ ?x. p x`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_SEQUENTIALLY = prove
 (`!p. eventually p sequentially <=> ?N. !n. N <= n ==> p n`,
  REWRITE_TAC[eventually; SEQUENTIALLY; GE; LE_REFL;
    TRIVIAL_LIMIT_SEQUENTIALLY] THEN  MESON_TAC[LE_REFL]);;

let ALWAYS_EVENTUALLY = prove
 (`(!x. p x) ==> eventually p net`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[eventually; trivial_limit] THEN
  MESON_TAC[]);;

let EVENTUALLY_AND = prove
 (`!net:(A net) p q.
        eventually (\x. p x /\ q x) net <=>
        eventually p net /\ eventually q net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually] THEN
  ASM_CASES_TAC `trivial_limit(net:(A net))` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN SIMP_TAC[NET_DILEMMA] THEN MESON_TAC[]);;

let EVENTUALLY_MONO = prove
 (`!net:(A net) p q.
        (!x. p x ==> q x) /\ eventually p net
        ==> eventually q net`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_MP = prove
 (`!net:(A net) p q.
        eventually (\x. p x ==> q x) net /\ eventually p net
        ==> eventually q net`,
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_FALSE = prove
 (`!net. eventually (\x. F) net <=> trivial_limit net`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_TRUE = prove
 (`!net. eventually (\x. T) net <=> T`,
  REWRITE_TAC[eventually; trivial_limit] THEN MESON_TAC[]);;

let NOT_EVENTUALLY = prove
 (`!net p. (!x. ~(p x)) /\ ~(trivial_limit net) ==> ~(eventually p net)`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_FORALL = prove
 (`!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
             !a. a IN s ==> eventually (p a) net)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; EVENTUALLY_AND; ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`b:B`; `t:B->bool`] THEN
  ASM_CASES_TAC `t:B->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; EVENTUALLY_TRUE]);;

let FORALL_EVENTUALLY = prove
 (`!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> ((!a. a IN s ==> eventually (p a) net) <=>
             eventually (\x. !a. a IN s ==> p a x) net)`,
  SIMP_TAC[EVENTUALLY_FORALL]);;

(* ------------------------------------------------------------------------- *)
(* Metric spaces.                                                            *)
(* ------------------------------------------------------------------------- *)

let is_metric_space = new_definition
  `is_metric_space (s,d) <=>
   (!x y:A. x IN s /\ y IN s ==> &0 <= d(x,y)) /\
   (!x y. x IN s /\ y IN s ==> (d(x,y) = &0 <=> x = y)) /\
   (!x y. x IN s /\ y IN s ==> d(x,y) = d(y,x)) /\
   (!x y z. x IN s /\ y IN s /\ z IN s ==> d(x,z) <= d(x,y) + d(y,z))`;;

let metric_tybij =
 (new_type_definition "metric" ("metric","dest_metric") o prove)
 (`?m:(A->bool)#(A#A->real). is_metric_space m`,
  EXISTS_TAC `({}:A->bool,(\p:A#A. &0))` THEN
  REWRITE_TAC[is_metric_space; NOT_IN_EMPTY]);;

let IS_METRIC_SPACE_SUBSPACE = prove
 (`!(s:A->bool) d. is_metric_space (s,d) ==>
                   (! s'. s' SUBSET s ==> is_metric_space (s',d))`,
  SIMP_TAC[SUBSET; is_metric_space]);;

let mspace = new_definition
  `!m:A metric. mspace m = FST (dest_metric m)`;;

let mdist = new_definition
  `!m:A metric. mdist m = SND (dest_metric m)`;;

let METRIC = prove
 (`!s d. is_metric_space (s:A->bool,d)
         ==> mspace (metric (s,d)) = s /\
             mdist (metric (s,d)) = d`,
  REWRITE_TAC[mspace; mdist] THEN MESON_TAC[metric_tybij; FST; SND]);;

let MSPACE = prove
 (`!s:A->bool d. is_metric_space (s,d) ==> mspace (metric (s,d)) = s`,
  SIMP_TAC[METRIC]);;

let MDIST = prove
 (`!s:A->bool d. is_metric_space (s,d) ==> mdist (metric (s,d)) = d`,
  SIMP_TAC[METRIC]);;

(* ------------------------------------------------------------------------- *)
(* Distance properties.                                                      *)
(* ------------------------------------------------------------------------- *)

let [MDIST_POS_LE; MDIST_0; MDIST_SYM; MDIST_TRIANGLE] =
  let FORALL_METRIC_THM = prove
   (`!P. (!m. P m) <=>
         (!s:A->bool d. is_metric_space(s,d) ==> P(metric (s,d)))`,
    REWRITE_TAC[GSYM FORALL_PAIR_THM; metric_tybij] THEN
    MESON_TAC[CONJUNCT1 metric_tybij]) in
  let METRIC_AXIOMS =
   (`!m. (!x y:A. x IN mspace m /\ y IN mspace m
                  ==> &0 <= mdist m (x,y)) /\
         (!x y. x IN mspace m /\ y IN mspace m
                ==> (mdist m (x,y) = &0 <=> x = y)) /\
         (!x y. x IN mspace m /\ y IN mspace m
                ==> mdist m (x,y) = mdist m (y,x)) /\
         (!x y z. x IN mspace m /\ y IN mspace m /\ z IN mspace m
                  ==> mdist m (x,z) <= mdist m (x,y) + mdist m (y,z))`,
    SIMP_TAC[FORALL_METRIC_THM; MSPACE; MDIST; is_metric_space]) in
  (CONJUNCTS o REWRITE_RULE [FORALL_AND_THM] o prove) METRIC_AXIOMS;;

let REAL_ABS_MDIST = prove
 (`!m x y:A. x IN mspace m /\ y IN mspace m
             ==> abs(mdist m (x,y)) = mdist m (x,y)`,
  SIMP_TAC[REAL_ABS_REFL; MDIST_POS_LE]);;

let MDIST_POS_LT = prove
 (`!m x y:A. x IN mspace m /\ y IN mspace m /\ ~(x=y)
             ==> &0 < mdist m (x,y)`,
  SIMP_TAC [REAL_LT_LE; MDIST_POS_LE] THEN MESON_TAC[MDIST_0]);;

let MDIST_REFL = prove
 (`!m x:A. x IN mspace m ==> mdist m (x,x) = &0`,
  SIMP_TAC[MDIST_0]);;

let MDIST_REVERSE_TRIANGLE = prove
 (`!m x y z:A. x IN mspace m /\ y IN mspace m /\ z IN mspace m
               ==> abs(mdist m (x,y) - mdist m (y,z)) <= mdist m (x,z)`,
  GEN_TAC THEN
  CLAIM_TAC "rmk"
    `!x y z:A. x IN mspace m /\ y IN mspace m /\ z IN mspace m
               ==> mdist m (x,y) - mdist m (y,z) <= mdist m (x,z)` THEN
  REPEAT STRIP_TAC THENL
  [REWRITE_TAC[REAL_LE_SUB_RADD] THEN ASM_MESON_TAC[MDIST_TRIANGLE; MDIST_SYM];
   REWRITE_TAC[REAL_ABS_BOUNDS;
               REAL_ARITH `!a b c. --a <= b - c <=> c - a <= b`] THEN
   ASM_MESON_TAC[MDIST_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Open ball.                                                                *)
(* ------------------------------------------------------------------------- *)

let mball = new_definition
  `mball m (x:A,r) =
   {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r}`;;

let IN_MBALL = prove
 (`!m x y:A r.
     y IN mball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r`,
  REWRITE_TAC[mball; IN_ELIM_THM]);;

let CENTRE_IN_MBALL = prove
 (`!m x:A r. &0 < r /\ x IN mspace m ==> x IN mball m (x,r)`,
  SIMP_TAC[IN_MBALL; MDIST_REFL; real_gt]);;

let CENTRE_IN_MBALL_EQ = prove
 (`!m x:A r. x IN mball m (x,r) <=> x IN mspace m /\ &0 < r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MBALL] THEN
  ASM_CASES_TAC `x:A IN mspace m` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MDIST_REFL]);;

let MBALL_SUBSET_MSPACE = prove
 (`!m (x:A) r. mball m (x,r) SUBSET mspace m`,
  SIMP_TAC[SUBSET; IN_MBALL]);;

let MBALL_EMPTY = prove
 (`!m x:A r. r <= &0 ==> mball m (x,r) = {}`,
  REWRITE_TAC[IN_MBALL; EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[MDIST_POS_LE; REAL_ARITH `!x. ~(r <= &0 /\ &0 <= x /\ x < r)`]);;

let MBALL_EMPTY_ALT = prove
 (`!m x:A r. ~(x IN mspace m) ==> mball m (x,r) = {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_MBALL] THEN MESON_TAC[]);;

let MBALL_EQ_EMPTY = prove
 (`!m x:A r. mball m (x,r) = {} <=> ~(x IN mspace m) \/ r <= &0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [MP_TAC CENTRE_IN_MBALL THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN SET_TAC[];
   STRIP_TAC THEN ASM_SIMP_TAC[MBALL_EMPTY; MBALL_EMPTY_ALT]]);;

let MBALL_SUBSET = prove
 (`!m x y:A a b. y IN mspace m /\ mdist m (x,y) + a <= b
                 ==> mball m (x,a) SUBSET mball m (y,b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:A IN mspace m` THENL
  [STRIP_TAC; ASM SET_TAC [MBALL_EMPTY_ALT]] THEN
  ASM_REWRITE_TAC[SUBSET; IN_MBALL] THEN FIX_TAC "[z]" THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CUT_TAC `mdist m (y,z) <= mdist m (x:A,y) + mdist m (x,z)` THENL
  [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[MDIST_SYM; MDIST_TRIANGLE]]);;

let DISJOINT_MBALL = prove
 (`!m x:A x' r r'. r + r' <= mdist m (x,x')
             ==> DISJOINT (mball m (x,r)) (mball m (x',r'))`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_MBALL;
              NOT_IN_EMPTY; CONJ_ACI] THEN
  INTRO_TAC "!m x x' r r'; HPrr'; !x''; x x' x'' d1 d2" THEN
  SUBGOAL_THEN `mdist m (x:A,x') < r + r'`
    (fun th -> ASM_MESON_TAC[th; REAL_NOT_LE]) THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (x:A,x'') + mdist m (x'',x')` THEN
  ASM_SIMP_TAC[MDIST_TRIANGLE; MDIST_SYM] THEN
  HYP (MP_TAC o end_itlist CONJ) "d1 d2" [] THEN REAL_ARITH_TAC);;

let MBALL_SUBSET_CONCENTRIC = prove
 (`!m (x:A) r1 r2. r1 <= r2 ==> mball m (x,r1) SUBSET mball m (x,r2)`,
  SIMP_TAC[SUBSET; IN_MBALL] THEN MESON_TAC[REAL_LTE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Subspace of a metric space.                                               *)
(* ------------------------------------------------------------------------- *)

let submetric = new_definition
  `submetric (m:A metric) s = metric (s INTER mspace m, mdist m)`;;

let SUBMETRIC = prove
 (`(!m:A metric s. mspace (submetric m s) = s INTER mspace m) /\
   (!m:A metric s. mdist (submetric m s) = mdist m)`,
  CLAIM_TAC "metric"
    `!m:A metric s. is_metric_space (s INTER mspace m, mdist m)` THENL
  [REWRITE_TAC[is_metric_space; IN_INTER] THEN
   SIMP_TAC[MDIST_POS_LE; MDIST_0; MDIST_SYM; MDIST_TRIANGLE];
   ASM_SIMP_TAC[submetric; MSPACE; MDIST]]);;

let MBALL_SUBMETRIC = prove
 (`!m s x:A r. x IN s ==> mball (submetric m s) (x,r) = mball m (x,r) INTER s`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EXTENSION; IN_MBALL; IN_INTER; SUBMETRIC] THEN MESON_TAC[]);;

let SUBMETRIC_UNIV = prove
 (`submetric m (:A) = m`,
  REWRITE_TAC[submetric; INTER_UNIV; mspace; mdist; metric_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Metric topology                                                           *)
(* ------------------------------------------------------------------------- *)

let mtopology = new_definition
  `mtopology (m:A metric) =
   topology {u | u SUBSET mspace m /\
                 !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}`;;

let IS_TOPOLOGY_METRIC_TOPOLOGY = prove
 (`istopology {u | u SUBSET mspace m /\
                   !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}`,
  REWRITE_TAC[istopology; IN_ELIM_THM; NOT_IN_EMPTY; EMPTY_SUBSET] THEN
  CONJ_TAC THENL
  [INTRO_TAC "!s t; (s shp) (t thp)" THEN CONJ_TAC THENL
   [HYP SET_TAC "s t" []; ALL_TAC] THEN
   REWRITE_TAC[IN_INTER] THEN INTRO_TAC "!x; sx tx" THEN
   REMOVE_THEN "shp"
     (DESTRUCT_TAC "@r1. r1 rs" o C MATCH_MP (ASSUME `x:A IN s`)) THEN
   REMOVE_THEN "thp"
     (DESTRUCT_TAC "@r2. r2 rt" o C MATCH_MP (ASSUME `x:A IN t`)) THEN
   EXISTS_TAC `min r1 r2` THEN
   ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET_INTER] THEN
   ASM_MESON_TAC[REAL_MIN_MIN; MBALL_SUBSET_CONCENTRIC; SUBSET_TRANS];
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN MESON_TAC[]]);;

let OPEN_IN_MTOPOLOGY = prove
 (`!m:A metric u.
     open_in (mtopology m) u <=>
     u SUBSET mspace m /\
     (!x. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mtopology] THEN
  (SUBST1_TAC o REWRITE_RULE[IS_TOPOLOGY_METRIC_TOPOLOGY] o
  SPEC `{u | u SUBSET mspace m /\
             !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}` o
  CONJUNCT2)
  topology_tybij THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM IN] THEN REWRITE_TAC[IN_ELIM_THM]);;

let TOPSPACE_MTOPOLOGY = prove
 (`!m:A metric. topspace (mtopology m) = mspace m`,
  GEN_TAC THEN REWRITE_TAC[mtopology; topspace] THEN
  (SUBST1_TAC o REWRITE_RULE[IS_TOPOLOGY_METRIC_TOPOLOGY] o
  SPEC `{u | u SUBSET mspace m /\
             !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}` o
  CONJUNCT2)
  topology_tybij THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL
  [SET_TAC[]; ALL_TAC] THEN
  INTRO_TAC "x" THEN EXISTS_TAC `mspace (m:A metric)` THEN
  ASM_REWRITE_TAC[MBALL_SUBSET_MSPACE; SUBSET_REFL] THEN
  MESON_TAC[REAL_LT_01]);;

let OPEN_IN_MBALL = prove
 (`!m (x:A) r. open_in (mtopology m) (mball m (x,r))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < (r:real)` THENL
  [ALL_TAC; ASM_SIMP_TAC[MBALL_EMPTY; GSYM REAL_NOT_LT; OPEN_IN_EMPTY]] THEN
  REWRITE_TAC[OPEN_IN_MTOPOLOGY; MBALL_SUBSET_MSPACE; IN_MBALL; SUBSET] THEN
  INTRO_TAC "![y]; x y xy" THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `r - mdist m (x:A,y)` THEN CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  INTRO_TAC "![z]; z lt" THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (x:A,y) + mdist m (y,z)` THEN
  ASM_SIMP_TAC[MDIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC);;

let MTOPOLOGY_SUBMETRIC = prove
 (`!m:A metric s. mtopology (submetric m s) = subtopology (mtopology m) s`,
  REWRITE_TAC[TOPOLOGY_EQ] THEN INTRO_TAC "!m s [u]" THEN
  EQ_TAC THEN INTRO_TAC "hp" THENL
  [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
   EXISTS_TAC
     `UNIONS {mball m (c:A,r) | c,r | mball m (c,r) INTER s SUBSET u}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN
    INTRO_TAC "![t]; @c r. sub t" THEN REMOVE_THEN "t" SUBST_VAR_TAC THEN
    MATCH_ACCEPT_TAC OPEN_IN_MBALL;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    HYP_TAC "hp: (us um) hp"
      (REWRITE_RULE[OPEN_IN_MTOPOLOGY; SUBMETRIC; SUBSET_INTER]) THEN
    ASM_REWRITE_TAC[SUBSET_INTER] THEN REWRITE_TAC[SUBSET] THEN
    INTRO_TAC "!x; x" THEN
    USE_THEN "x" (HYP_TAC "hp: @r. rpos sub" o C MATCH_MP) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `mball m (x:A,r)` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`x:A`; `r:real`] THEN
     IMP_REWRITE_TAC [GSYM MBALL_SUBMETRIC] THEN ASM SET_TAC[];
     MATCH_MP_TAC CENTRE_IN_MBALL THEN ASM SET_TAC[]]];
   ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_MTOPOLOGY; SUBMETRIC; SUBSET_INTER] THEN
  HYP_TAC "hp: @t. t u" (REWRITE_RULE[OPEN_IN_SUBTOPOLOGY]) THEN
  REMOVE_THEN "u" SUBST_VAR_TAC THEN
  HYP_TAC "t: tm r" (REWRITE_RULE[OPEN_IN_MTOPOLOGY]) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN INTRO_TAC "!x; xt xs" THEN
  USE_THEN "xt" (HYP_TAC "r: @r. rpos sub" o C MATCH_MP) THEN
  EXISTS_TAC `r:real` THEN IMP_REWRITE_TAC[MBALL_SUBMETRIC] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let CLOSED_IN_METRIC = prove
 (`!m c:A->bool.
     closed_in (mtopology m) c <=>
     c SUBSET mspace m /\
     (!x. x IN mspace m DIFF c ==> ?r. &0 < r /\ DISJOINT c (mball m (x,r)))`,
  REWRITE_TAC[closed_in; OPEN_IN_MTOPOLOGY; DISJOINT; TOPSPACE_MTOPOLOGY] THEN
  MP_TAC MBALL_SUBSET_MSPACE THEN ASM SET_TAC[]);;

let mcball = new_definition
  `mcball m (x:A,r) =
   {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) <= r}`;;

let IN_MCBALL = prove
 (`!m (x:A) r y.
     y IN mcball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) <= r`,
  REWRITE_TAC[mcball; IN_ELIM_THM]);;

let CENTRE_IN_MCBALL = prove
 (`!m x:A r. &0 <= r /\ x IN mspace m ==> x IN mcball m (x,r)`,
  SIMP_TAC[IN_MCBALL; MDIST_REFL]);;

let CENTRE_IN_MCBALL_EQ = prove
 (`!m x:A r. x IN mcball m (x,r) <=> x IN mspace m /\ &0 <= r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MCBALL] THEN
  ASM_CASES_TAC `x:A IN mspace m` THEN ASM_SIMP_TAC[MDIST_REFL]);;

let MCBALL_EMPTY = prove
 (`!m (x:A) r. r < &0 ==> mcball m (x,r) = {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_MCBALL] THEN
  MESON_TAC[REAL_LET_TRANS; MDIST_POS_LE; REAL_NOT_LT]);;

let MCBALL_EMPTY_ALT = prove
 (`!m (x:A) r. ~(x IN mspace m) ==> mcball m (x,r) = {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_MCBALL; DE_MORGAN_THM] THEN
  MESON_TAC[]);;

let MCBALL_SUBSET_MSPACE = prove
 (`!m (x:A) r. mcball m (x,r) SUBSET (mspace m)`,
  REWRITE_TAC[mcball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let MBALL_SUBSET_MCBALL = prove
 (`!m x:A r. mball m (x,r) SUBSET mcball m (x,r)`,
  SIMP_TAC[SUBSET; IN_MBALL; IN_MCBALL; REAL_LT_IMP_LE]);;

let MCBALL_SUBSET = prove
 (`!m x y:A a b. y IN mspace m /\ mdist m (x,y) + a <= b
                 ==> mcball m (x,a) SUBSET mcball m (y,b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:A IN mspace m` THENL
  [STRIP_TAC; ASM SET_TAC [MCBALL_EMPTY_ALT]] THEN
  ASM_REWRITE_TAC[SUBSET; IN_MCBALL] THEN FIX_TAC "[z]" THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CUT_TAC `mdist m (y,z) <= mdist m (x:A,y) + mdist m (x,z)` THENL
  [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[MDIST_SYM; MDIST_TRIANGLE]]);;

let MCBALL_SUBSET_CONCENTRIC = prove
 (`!m (x:A) a b. a <= b ==> mcball m (x,a) SUBSET mcball m (x,b)`,
  SIMP_TAC[SUBSET; IN_MCBALL] THEN MESON_TAC[REAL_LE_TRANS]);;

let MCBALL_SUBSET_MBALL = prove
 (`!m x y:A a b.
     y IN mspace m /\ mdist m (x,y) + a < b
     ==> mcball m (x,a) SUBSET mball m (y,b)`,
  INTRO_TAC "!m x y a b; y lt" THEN ASM_CASES_TAC `x:A IN mspace m` THENL
  [POP_ASSUM (LABEL_TAC "x");
   ASM_SIMP_TAC[MCBALL_EMPTY_ALT; EMPTY_SUBSET]] THEN
  ASM_REWRITE_TAC[SUBSET; IN_MCBALL; IN_MBALL] THEN
  INTRO_TAC "![z]; z le" THEN HYP REWRITE_TAC "z" [] THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (y:A,x) + mdist m (x,z)` THEN
  ASM_SIMP_TAC[MDIST_TRIANGLE] THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (x:A,y) + a` THEN
  HYP REWRITE_TAC "lt" [] THEN HYP SIMP_TAC "x y" [MDIST_SYM] THEN
  ASM_REAL_ARITH_TAC);;

let MCBALL_SUBSET_MBALL_CONCENTRIC = prove
 (`!m x:A a b. a < b ==> mcball m (x,a) SUBSET mball m (x,b)`,
  INTRO_TAC "!m x a b; lt" THEN ASM_CASES_TAC `x:A IN mspace m` THENL
  [POP_ASSUM (LABEL_TAC "x");
   ASM_SIMP_TAC[MCBALL_EMPTY_ALT; EMPTY_SUBSET]] THEN
  MATCH_MP_TAC MCBALL_SUBSET_MBALL THEN ASM_SIMP_TAC[MDIST_REFL] THEN
  ASM_REAL_ARITH_TAC);;

let CLOSED_IN_MCBALL = prove
 (`!m:A metric x r. closed_in (mtopology m) (mcball m (x,r))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CLOSED_IN_METRIC; MCBALL_SUBSET_MSPACE; DIFF; IN_ELIM_THM;
              IN_MCBALL; DE_MORGAN_THM; REAL_NOT_LE] THEN
  FIX_TAC "[y]" THEN
  MAP_EVERY ASM_CASES_TAC [`x:A IN mspace m`; `y:A IN mspace m`] THEN
  ASM_REWRITE_TAC[] THENL
  [ALL_TAC;
   ASM_SIMP_TAC[MCBALL_EMPTY_ALT; DISJOINT_EMPTY] THEN
   MESON_TAC[REAL_LT_01]] THEN
  INTRO_TAC "lt" THEN EXISTS_TAC `mdist m (x:A,y) - r` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; DISJOINT; IN_INTER; NOT_IN_EMPTY;
              IN_MBALL; IN_MCBALL] THEN
  FIX_TAC "[z]" THEN ASM_CASES_TAC `z:A IN mspace m` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mdist m (x,y) <= mdist m (x:A,z) + mdist m (z,y)` MP_TAC THENL
  [ASM_SIMP_TAC[MDIST_TRIANGLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MDIST_SYM] THEN ASM_REAL_ARITH_TAC);;

let MCBALL_SUBMETRIC = prove
 (`!m s x:A r.
     x IN s ==> mcball (submetric m s) (x,r) = mcball m (x,r) INTER s`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EXTENSION; IN_MCBALL; IN_INTER; SUBMETRIC] THEN
  MESON_TAC[]);;

let OPEN_IN_MTOPOLOGY_MCBALL = prove
 (`!m u. open_in (mtopology m) (u:A->bool) <=>
         u SUBSET mspace m /\
         (!x. x IN u ==> (?r. &0 < r /\ mcball m (x,r) SUBSET u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN
  ASM_CASES_TAC `u:A->bool SUBSET mspace m` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
  [INTRO_TAC "hp; !x; x" THEN
   REMOVE_THEN "x" (HYP_TAC "hp: @r. rpos sub" o C MATCH_MP) THEN
   EXISTS_TAC `r / &2` THEN
   HYP REWRITE_TAC "rpos" [REAL_HALF] THEN
   TRANS_TAC SUBSET_TRANS `mball m (x:A,r)` THEN HYP REWRITE_TAC "sub" [] THEN
   MATCH_MP_TAC MCBALL_SUBSET_MBALL_CONCENTRIC THEN
   ASM_REAL_ARITH_TAC;
   INTRO_TAC "hp; !x; x" THEN
   REMOVE_THEN "x" (HYP_TAC "hp: @r. rpos sub" o C MATCH_MP) THEN
   EXISTS_TAC `r:real` THEN HYP REWRITE_TAC "rpos" [] THEN
   TRANS_TAC SUBSET_TRANS `mcball m (x:A,r)` THEN
   HYP REWRITE_TAC "sub" [MBALL_SUBSET_MCBALL]]);;

(* ------------------------------------------------------------------------- *)
(* Spheres in metric spaces.                                                 *)
(* ------------------------------------------------------------------------- *)

let msphere = new_definition
  `msphere m (x:A,e) = {y | mdist m (x,y) = e}`;;

(* ------------------------------------------------------------------------- *)
(* Bounded sets.                                                             *)
(* ------------------------------------------------------------------------- *)

let mbounded = new_definition
  `mbounded m s <=> (?c:A b. s SUBSET mcball m (c,b))`;;

let MBOUNDED_SUBSET = prove
 (`!m s t:A->bool. mbounded m t /\ s SUBSET t ==> mbounded m s`,
  REWRITE_TAC[mbounded] THEN SET_TAC[]);;

let MBOUNDED_SUBSET_MSPACE = prove
 (`!m s:A->bool. mbounded m s ==> s SUBSET mspace m`,
  REWRITE_TAC[mbounded] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC SUBSET_TRANS `mcball m (c:A,b)` THEN
  ASM_REWRITE_TAC[MCBALL_SUBSET_MSPACE]);;

let MBOUNDED = prove
 (`!m s. mbounded m s <=>
         s = {} \/
         (!x:A. x IN s ==> x IN mspace m) /\
         (?c b. c IN mspace m /\ (!x. x IN s ==> mdist m (c,x) <= b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mbounded; SUBSET; IN_MCBALL] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM SET_TAC[]);;

let MBOUNDED_EMPTY = prove
 (`!m:A metric. mbounded m {}`,
  REWRITE_TAC[mbounded; EMPTY_SUBSET]);;

let MBOUNDED_MCBALL = prove
 (`!m:A metric c b. mbounded m (mcball m (c,b))`,
  REWRITE_TAC[mbounded] THEN MESON_TAC[SUBSET_REFL]);;

let MBOUNDED_MBALL = prove
 (`!m:A metric c b. mbounded m (mball m (c,b))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MBOUNDED_SUBSET THEN
  EXISTS_TAC `mcball m (c:A,b)` THEN
  REWRITE_TAC[MBALL_SUBSET_MCBALL; MBOUNDED_MCBALL]);;

let MBOUNDED_INSERT = prove
 (`!m a:A s. mbounded m (a INSERT s) <=> a IN mspace m /\ mbounded m s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MBOUNDED; NOT_INSERT_EMPTY; IN_INSERT] THEN
  ASM_CASES_TAC `a:A IN mspace m` THEN ASM_REWRITE_TAC[] THENL
  [ALL_TAC; ASM_MESON_TAC[]] THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY] THENL [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c:A`; `max b (mdist m (c:A,a))`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MAX_MAX] THEN
  TRANS_TAC REAL_LE_TRANS `b:real` THEN ASM_SIMP_TAC[REAL_MAX_MAX]);;

let MBOUNDED_INTER = prove
 (`!m:A metric s t. mbounded m s /\ mbounded m t ==> mbounded m (s INTER t)`,
  REWRITE_TAC[mbounded] THEN SET_TAC[]);;

let MBOUNDED_UNION = prove
 (`!m:A metric s t. mbounded m (s UNION t) <=> mbounded m s /\ mbounded m t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mbounded] THEN EQ_TAC THENL
  [SET_TAC[]; INTRO_TAC "(@c1 b1. s) (@c2 b2. t)"] THEN
  ASM_CASES_TAC
    `&0 <= b1 /\ &0 <= b2 /\ c1:A IN mspace m /\ c2 IN mspace m` THENL
  [POP_ASSUM STRIP_ASSUME_TAC;
   POP_ASSUM MP_TAC THEN REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
   ASM SET_TAC [MCBALL_EMPTY; MCBALL_EMPTY_ALT]] THEN
  MAP_EVERY EXISTS_TAC [`c1:A`; `b1 + b2 + mdist m (c1:A,c2)`] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
  [TRANS_TAC SUBSET_TRANS `mcball m (c1:A,b1)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MCBALL_SUBSET_CONCENTRIC THEN
   CUT_TAC `&0 <= mdist m (c1:A,c2)` THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[MDIST_POS_LE]];
   TRANS_TAC SUBSET_TRANS `mcball m (c2:A,b2)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MCBALL_SUBSET THEN ASM_SIMP_TAC[MDIST_SYM] THEN
   ASM_REAL_ARITH_TAC]);;

let MBOUNDED_IFF_FINITE_DIAMETER = prove
 (`!m:A metric s. mbounded m s <=>
                  s SUBSET mspace m /\
                  (?b. !x y. x IN s /\ y IN s ==> mdist m (x,y) <= b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mbounded; SUBSET; IN_MCBALL] THEN
  EQ_TAC THENL
  [INTRO_TAC "@c b. hp" THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `b + b:real` THEN INTRO_TAC "!x y; x y" THEN
   TRANS_TAC REAL_LE_TRANS `mdist m (x:A,c) + mdist m (c,y)` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[MDIST_TRIANGLE];
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_MESON_TAC[MDIST_SYM]];
   ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
   POP_ASSUM (DESTRUCT_TAC "@a. a" o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
   INTRO_TAC "inc (@b. bound)" THEN
   MAP_EVERY EXISTS_TAC [`a:A`; `b:real`] THEN ASM_SIMP_TAC[]]);;

let MBOUNDED_SUBMETRIC = prove
 (`!m:A metric s.
     mbounded (submetric m s) t <=> mbounded m (s INTER t) /\ t SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MBOUNDED_IFF_FINITE_DIAMETER; SUBMETRIC] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A decision procedure for metric spaces.                                   *)
(* ------------------------------------------------------------------------- *)

let METRIC_ARITH : term -> thm =
  let SUP_CONV =
    let conv0 = REWR_CONV SUP_INSERT_INSERT
    and conv1 = REWR_CONV SUP_SING in
    conv1 ORELSEC (conv0 THENC REPEATC conv0 THENC TRY_CONV conv1) in
  let MAXDIST_THM = prove
   (`!m s x y:A.
       mbounded m s /\ x IN s /\ y IN s
       ==> mdist m (x,y) =
           sup (IMAGE (\a. abs(mdist m (x,a) - mdist m (a,y))) s)`,
    REPEAT GEN_TAC THEN INTRO_TAC "bnd x y" THEN
    MATCH_MP_TAC (GSYM SUP_UNIQUE) THEN
    CLAIM_TAC "inc" `!p:A. p IN s ==> p IN mspace m` THENL
    [HYP SET_TAC "bnd" [MBOUNDED_SUBSET_MSPACE]; ALL_TAC] THEN
    GEN_TAC THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN EQ_TAC THENL
    [INTRO_TAC "le; ![z]; z" THEN
     TRANS_TAC REAL_LE_TRANS `mdist m (x:A,y)` THEN
     ASM_SIMP_TAC[MDIST_REVERSE_TRIANGLE];
     DISCH_THEN (MP_TAC o C MATCH_MP (ASSUME `y:A IN s`)) THEN
     ASM_SIMP_TAC[MDIST_REFL; REAL_SUB_RZERO; REAL_ABS_MDIST]])
  and METRIC_EQ_THM = prove
   (`!m s x y:A.
       s SUBSET mspace m /\ x IN s /\ y IN s
       ==> (x = y <=> (!a. a IN s ==> mdist m (x,a) = mdist m (y,a)))`,
    INTRO_TAC "!m s x y; sub sx sy" THEN EQ_TAC THEN SIMP_TAC[] THEN
    DISCH_THEN (MP_TAC o SPEC `y:A`) THEN
    CLAIM_TAC "x y" `x:A IN mspace m /\ y IN mspace m` THENL
    [ASM SET_TAC []; ASM_SIMP_TAC[MDIST_REFL; MDIST_0]]) in
  let CONJ1_CONV : conv -> conv =
    let TRUE_CONJ_CONV = REWR_CONV (MESON [] `T /\ p <=> p`) in
    fun conv -> LAND_CONV conv THENC TRUE_CONJ_CONV in
  let IN_CONV : conv =
    let DISJ_TRUE_CONV = REWR_CONV (MESON [] `p \/ T <=> T`)
    and TRUE_DISJ_CONV = REWR_CONV (MESON [] `T \/ p <=> T`) in
    let REFL_CONV = REWR_CONV (MESON [] `x:A = x <=> T`) in
    let conv0 = REWR_CONV (EQF_INTRO (SPEC_ALL NOT_IN_EMPTY)) in
    let conv1 = REWR_CONV IN_INSERT in
    let conv2 = LAND_CONV REFL_CONV THENC TRUE_DISJ_CONV in
    let rec IN_CONV tm =
      (conv0 ORELSEC
       (conv1 THENC
        (conv2 ORELSEC
         (RAND_CONV IN_CONV THENC DISJ_TRUE_CONV)))) tm in
    IN_CONV
  and IMAGE_CONV : conv =
    let pth0,pth1 = CONJ_PAIR IMAGE_CLAUSES in
    let conv0 = REWR_CONV pth0
    and conv1 = REWR_CONV pth1 THENC TRY_CONV (LAND_CONV BETA_CONV) in
    let rec IMAGE_CONV tm =
      (conv0 ORELSEC (conv1 THENC RAND_CONV IMAGE_CONV)) tm in
    IMAGE_CONV in
  let SUBSET_CONV : conv -> conv =
    let conv0 = REWR_CONV (EQT_INTRO (SPEC_ALL EMPTY_SUBSET)) in
    let conv1 = REWR_CONV INSERT_SUBSET in
    fun conv ->
      let conv2 = conv1 THENC CONJ1_CONV conv in
      REPEATC conv2 THENC conv0 in
  let rec prove_hyps th =
    match hyp th with
    | [] -> th
    | htm :: _ ->
        let emth = SPEC htm EXCLUDED_MIDDLE in
        let nhp = EQF_INTRO (ASSUME (mk_neg htm)) in
        let nth1 = (SUBS_CONV [nhp] THENC PRESIMP_CONV) (concl th) in
        let nth2 = MESON [nhp] (rand (concl nth1)) in
        let nth = EQ_MP (SYM nth1) nth2 in
        prove_hyps(DISJ_CASES emth th nth) in
  let rec guess_metric tm =
    match tm with
    | Comb(Const("mdist",_),m) -> m
    | Comb(Const("mspace",_),m) -> m
    | Comb(s,t) -> (try guess_metric s with Failure _ -> guess_metric t)
    | Abs(_, bd) -> guess_metric bd
    | _ -> failwith "metric not found" in
  let find_mdist mtm =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("mdist",_),pmtm),p) when pmtm = mtm -> [tm]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find
  and find_eq mty =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("=",ty),_),_) when fst(dest_fun_ty ty) = mty -> [tm]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find
  and find_points mtm =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("mdist",_),pmtm),p) when pmtm = mtm ->
          let x,y = dest_pair p in
          if x = y then [x] else [x;y]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find in
  let prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PURE_REWRITE_CONV[FORALL_SIMP; EXISTS_SIMP] THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV `(/\)` CONDS_CELIM_CONV THENC
    PRESIMP_CONV THENC
    GEN_REWRITE_CONV REDEPTH_CONV
      [AND_FORALL_THM; LEFT_AND_FORALL_THM; RIGHT_AND_FORALL_THM;
       LEFT_OR_FORALL_THM; RIGHT_OR_FORALL_THM] THENC
    PRENEX_CONV
  and real_poly_conv =
    let eths = REAL_ARITH
      `(x = y <=> x - y = &0) /\
       (x < y <=> y - x > &0) /\
       (x > y <=> x - y > &0) /\
       (x <= y <=> y - x >= &0) /\
       (x >= y <=> x - y >= &0)` in
    GEN_REWRITE_CONV I [eths] THENC LAND_CONV REAL_POLY_CONV
  and augment_mdist_pos_thm =
    MESON [] `p ==> (q <=> r) ==> (q <=> (p ==> r))` in
  fun tm ->
    let mtm = guess_metric tm in
    let mty = hd(snd(dest_type(type_of mtm))) in
    let mspace_tm = mk_icomb(mk_const("mspace",[]),mtm) in
    let metric_eq_thm = ISPEC mtm METRIC_EQ_THM
    and mk_in_mspace_th =
      let in_tm = mk_const("IN",[mty,aty]) in
      fun pt -> ASSUME (mk_comb(mk_comb(in_tm,pt),mspace_tm)) in
    let th0 = prenex_conv tm in
    let tm0 = rand (concl th0) in
    let avs,bod = strip_forall tm0 in
    let points = find_points mtm bod in
    let in_mspace_conv = GEN_REWRITE_CONV I (map mk_in_mspace_th points) in
    let in_mspace2_conv = CONJ1_CONV in_mspace_conv THENC in_mspace_conv in
    let MDIST_REFL_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm MDIST_REFL) in
      fun tm -> MP_CONV in_mspace_conv (pconv tm)
    and MDIST_SYM_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm MDIST_SYM) in
      fun tm -> let x,y = dest_pair (rand tm) in
                if x <= y then failwith "MDIST_SYM_CONV" else
                MP_CONV in_mspace2_conv (pconv tm)
    and MBOUNDED_CONV =
      let conv0 = REWR_CONV (EQT_INTRO (ISPEC mtm MBOUNDED_EMPTY)) in
      let conv1 = REWR_CONV (ISPEC mtm MBOUNDED_INSERT) in
      let rec mbounded_conv tm =
        try conv0 tm with Failure _ ->
        (conv1 THENC CONJ1_CONV in_mspace_conv THENC mbounded_conv) tm in
      mbounded_conv in
    let REFL_SYM_CONV = MDIST_REFL_CONV ORELSEC MDIST_SYM_CONV in
    let ABS_MDIST_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm REAL_ABS_MDIST) in
      fun tm -> MP_CONV in_mspace2_conv (pconv tm) in
    let metric_eq_prerule =
      (CONV_RULE o BINDER_CONV o BINDER_CONV)
      (LAND_CONV (CONJ1_CONV (SUBSET_CONV in_mspace_conv)) THENC
       RAND_CONV (REWRITE_CONV[FORALL_IN_INSERT; NOT_IN_EMPTY])) in
    let MAXDIST_CONV =
      let maxdist_thm = ISPEC mtm MAXDIST_THM
      and ante_conv =
        CONJ1_CONV MBOUNDED_CONV THENC CONJ1_CONV IN_CONV THENC IN_CONV
      and image_conv =
        IMAGE_CONV THENC ONCE_DEPTH_CONV REFL_SYM_CONV THENC
        PURE_REWRITE_CONV
          [REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_SUB_REFL;
           REAL_ABS_0; REAL_ABS_NEG; REAL_ABS_SUB; INSERT_AC] THENC
        ONCE_DEPTH_CONV ABS_MDIST_CONV THENC
        PURE_REWRITE_CONV[INSERT_AC] in
      let sup_conv = RAND_CONV image_conv THENC SUP_CONV in
      fun fset_tm ->
        let maxdist_th = SPEC fset_tm maxdist_thm in
        fun tm ->
          let th0 = MP_CONV ante_conv (IMP_REWR_CONV maxdist_th tm) in
          let tm0 = rand (concl th0) in
          let th1 = sup_conv tm0 in
          TRANS th0 th1 in
    let AUGMENT_MDISTS_POS_RULE =
      let mdist_pos_le = ISPEC mtm MDIST_POS_LE in
      let augment_rule : term -> thm -> thm =
        let mk_mdist_pos_thm tm =
          let xtm,ytm = dest_pair (rand tm) in
          let pth = SPECL[xtm;ytm] mdist_pos_le in
          MP_CONV (CONJ1_CONV in_mspace_conv THENC in_mspace_conv) pth in
        fun mdist_tm ->
          let ith =
            MATCH_MP augment_mdist_pos_thm (mk_mdist_pos_thm mdist_tm) in
          fun th -> MATCH_MP ith th in
      fun th ->
        let mdist_thl = find_mdist mtm (concl th) in
        itlist augment_rule mdist_thl th in
    let BASIC_METRIC_ARITH (tm : term) : thm =
      let mdist_tms = find_mdist mtm tm in
      let th0 =
        let eqs =
          mapfilter (MDIST_REFL_CONV ORELSEC MDIST_SYM_CONV) mdist_tms in
        (ONCE_DEPTH_CONV in_mspace_conv THENC PRESIMP_CONV THENC
         SUBS_CONV eqs THENC REAL_RAT_REDUCE_CONV THENC
         ONCE_DEPTH_CONV real_poly_conv) tm in
      let tm0 = rand (concl th0) in
      let points = find_points mtm tm0 in
      let fset_tm = mk_setenum(points,mty) in
      let METRIC_EQ_CONV =
        let th = metric_eq_prerule (SPEC fset_tm metric_eq_thm) in
        fun tm ->
          let xtm,ytm = dest_eq tm in
          let th0 = SPECL[xtm;ytm] th in
          let th1 = MP_CONV (CONJ1_CONV IN_CONV THENC IN_CONV) th0 in
          let tm1 = rand (concl th1) in
          let th2 = ONCE_DEPTH_CONV REFL_SYM_CONV tm1 in
          TRANS th1 th2 in
      let eq1 = map (MAXDIST_CONV fset_tm) (find_mdist mtm tm0)
      and eq2 = map METRIC_EQ_CONV (find_eq mty tm0) in
      let th1 = AUGMENT_MDISTS_POS_RULE (SUBS_CONV (eq1 @ eq2) tm0) in
      let tm1 = rand (concl th1) in
      prove_hyps (EQ_MP (SYM th0) (EQ_MP (SYM th1) (REAL_ARITH tm1))) in
    let SIMPLE_METRIC_ARITH tm =
      let th0 = (WEAK_CNF_CONV THENC CONJ_CANON_CONV) tm in
      let tml =
        try conjuncts (rand (concl th0))
        with Failure s -> failwith("conjuncts "^s) in
      let th1 =
        try end_itlist CONJ (map BASIC_METRIC_ARITH tml)
        with Failure s -> failwith("end_itlist "^s) in
      EQ_MP (SYM th0) th1 in
    let elim_exists tm =
      let points = find_points mtm tm in
      let rec try_points v tm ptl =
        if ptl = [] then fail () else
        let xtm = hd ptl in
        try EXISTS (mk_exists(v,tm),xtm) (elim_exists (vsubst [xtm,v] tm))
        with Failure _ -> try_points v tm (tl ptl)
      and elim_exists tm =
        try let v,bd = dest_exists tm in
            try_points v bd points
        with Failure _ -> SIMPLE_METRIC_ARITH tm in
      elim_exists tm in
    EQ_MP (SYM th0) (GENL avs (elim_exists bod));;

let METRIC_ARITH_TAC = CONV_TAC METRIC_ARITH;;

let ASM_METRIC_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  METRIC_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Compact sets.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("compact_in",(12,"right"));;

let compact_in = new_definition
  `!top s:A->bool.
     s compact_in top <=>
     s SUBSET topspace top /\
     (!U. (!u. u IN U ==> open_in top u) /\ s SUBSET UNIONS U
          ==> (?V. FINITE V /\ V SUBSET U /\ s SUBSET UNIONS V))`;;

let COMPACT_IN_SUBSET_TOPSPACE = prove
 (`!top s:A->bool. s compact_in top ==> s SUBSET topspace top`,
  SIMP_TAC[compact_in]);;

let FINITE_IMP_COMPACT_IN = prove
 (`!top s:A->bool. s SUBSET topspace top /\ FINITE s ==> s compact_in top`,
  SIMP_TAC[compact_in] THEN INTRO_TAC "!top s; sub fin; !U; U s" THEN
  EXISTS_TAC `IMAGE (\x:A. @u. u IN U /\ x IN u) s` THEN
  HYP SIMP_TAC "fin" [FINITE_IMAGE] THEN ASM SET_TAC []);;

let EMPTY_IMP_COMPACT_IN = prove
 (`!top. {}:A->bool compact_in top`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
  REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET]);;

let CLOSED_COMPACT_IN = prove
 (`!top k c:A->bool. k compact_in top /\ c SUBSET k /\ closed_in top c
                     ==> c compact_in top`,
  INTRO_TAC "! *; cpt sub cl" THEN REWRITE_TAC[compact_in] THEN CONJ_TAC THENL
  [HYP SET_TAC "sub cpt" [compact_in]; INTRO_TAC "!U; U c"] THEN
  HYP_TAC "cpt: ksub cpt" (REWRITE_RULE[compact_in]) THEN
  REMOVE_THEN "cpt" (MP_TAC o
    SPEC `(topspace top DIFF c:A->bool) INSERT U`) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [CUT_TAC `open_in top (topspace top DIFF c:A->bool)` THENL
    [HYP SET_TAC "U" [IN_DIFF];
     HYP SIMP_TAC "cl" [OPEN_IN_DIFF; OPEN_IN_TOPSPACE]];
    HYP_TAC "cl: c' cl" (REWRITE_RULE[closed_in]) THEN
    REWRITE_TAC[SUBSET; IN_INSERT; IN_DIFF; IN_UNIONS] THEN
    INTRO_TAC "!x; x" THEN ASM_CASES_TAC `x:A IN c` THEN
    POP_ASSUM (LABEL_TAC "x'") THENL
    [HYP SET_TAC "c x'" [];
     EXISTS_TAC `topspace top DIFF c:A->bool` THEN
     ASM_REWRITE_TAC[] THEN ASM SET_TAC []]];
   INTRO_TAC "@V. fin v k" THEN
   EXISTS_TAC `V DELETE (topspace top DIFF c:A->bool)` THEN
   ASM_REWRITE_TAC[FINITE_DELETE] THEN
   CONJ_TAC THENL [ASM SET_TAC []; ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_DELETE] THEN ASM SET_TAC []]);;

let COMPACT_IN_IMP_MBOUNDED = prove
 (`!m s:A->bool. s compact_in (mtopology m) ==> mbounded m s`,
  REWRITE_TAC[compact_in; TOPSPACE_MTOPOLOGY; mbounded] THEN
  INTRO_TAC "!m s; s cpt" THEN ASM_CASES_TAC `s:A->bool = {}` THENL
  [ASM_REWRITE_TAC[EMPTY_SUBSET];
   POP_ASSUM (DESTRUCT_TAC "@a. a" o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY])] THEN
  CLAIM_TAC "a'" `a:A IN mspace m` THENL [ASM SET_TAC[]; EXISTS_TAC `a:A`] THEN
  REMOVE_THEN "cpt" (MP_TAC o SPEC `{mball m (a:A,&n) | n IN (:num)}`) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN; OPEN_IN_MBALL];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    INTRO_TAC "!x; x" THEN CLAIM_TAC "@n. n" `?n. mdist m (a:A,x) <= &n` THENL
    [MATCH_ACCEPT_TAC REAL_ARCH_SIMPLE;
     EXISTS_TAC `mball m (a:A,&n + &1)`] THEN
    CONJ_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_ADD; IN_UNIV] THEN MESON_TAC[];
     ASM_SIMP_TAC[IN_MBALL; REAL_ARITH `!x. x <= &n ==> x < &n + &1`] THEN
     ASM SET_TAC []]];
   ALL_TAC] THEN
  INTRO_TAC "@V. fin V cov" THEN
  CLAIM_TAC "@k. k" `?k. !v. v IN V ==> v = mball m (a:A,&(k v))` THENL
  [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN ASM SET_TAC [];
   ALL_TAC] THEN
  CLAIM_TAC "kfin" `FINITE (IMAGE (k:(A->bool)->num) V)` THENL
  [HYP SIMP_TAC "fin" [FINITE_IMAGE];
   HYP_TAC "kfin: @n. n" (REWRITE_RULE[num_FINITE])] THEN EXISTS_TAC `&n` THEN
  TRANS_TAC SUBSET_TRANS `UNIONS (V:(A->bool)->bool)` THEN
  HYP SIMP_TAC "cov" [UNIONS_SUBSET] THEN INTRO_TAC "![v]; v" THEN
  USE_THEN "v" (HYP_TAC "k" o C MATCH_MP) THEN REMOVE_THEN "k" SUBST1_TAC THEN
  TRANS_TAC SUBSET_TRANS `mball m (a:A,&n)` THEN
  REWRITE_TAC[MBALL_SUBSET_MCBALL] THEN MATCH_MP_TAC MBALL_SUBSET THEN
  ASM_SIMP_TAC[MDIST_REFL; REAL_ADD_LID; REAL_OF_NUM_LE] THEN
  HYP SET_TAC "n v" []);;

let COMPACT_IN_SUBTOPOLOGY_IMP_COMPACT = prove
 (`!top k s:A->bool.
     k compact_in subtopology top s ==> k compact_in top`,
  REWRITE_TAC[compact_in; TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN
  INTRO_TAC "!top k s; (k sub) cpt" THEN ASM_REWRITE_TAC[] THEN
  INTRO_TAC "!U; open cover" THEN
  HYP_TAC "cpt: +" (SPEC `{u INTER s | u | u:A->bool IN U}`) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[GSYM INTER_UNIONS; SUBSET_INTER] THEN
   REWRITE_TAC[IN_ELIM_THM; OPEN_IN_SUBTOPOLOGY] THEN
   INTRO_TAC "!u; @v. v ueq" THEN
   REMOVE_THEN "ueq" SUBST_VAR_TAC THEN EXISTS_TAC `v:A->bool` THEN
   REMOVE_THEN "v" (HYP_TAC "open" o C MATCH_MP) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "@V. fin V k" THEN EXISTS_TAC `IMAGE (\v:A->bool.
    if v IN V then @u. u IN U /\ v = u INTER s else {}) V` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_IMAGE] THEN INTRO_TAC "![u]; @v. ueq v" THEN
   REMOVE_THEN "ueq" SUBST_VAR_TAC THEN ASM_REWRITE_TAC[] THEN
   HYP_TAC "V" (REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   REMOVE_THEN "v" (HYP_TAC "V: @u. u veq" o C MATCH_MP) THEN
   REMOVE_THEN "veq" SUBST_VAR_TAC THEN HYP MESON_TAC "u" [];
   ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN INTRO_TAC "!x; x" THEN
  HYP_TAC "k" (REWRITE_RULE[SUBSET; IN_UNIONS]) THEN
  USE_THEN "x" (HYP_TAC "k: @v. v xINv" o C MATCH_MP) THEN
  LABEL_ABBREV_TAC `u:A->bool = @u. u IN U /\ v = u INTER s` THEN
  CLAIM_TAC "u' veq" `u:A->bool IN U /\ v = u INTER s` THENL
  [REMOVE_THEN "u" SUBST_VAR_TAC THEN
   CUT_TAC `?u:A->bool. u IN U /\ v = u INTER s` THENL
   [MESON_TAC[]; ALL_TAC] THEN
   HYP_TAC "V" (REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   USE_THEN "v" (HYP_TAC "V" o C MATCH_MP) THEN
   REMOVE_THEN "V" MATCH_ACCEPT_TAC;
   EXISTS_TAC `u:A->bool` THEN CONJ_TAC THENL
   [EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[];
    HYP SET_TAC "veq xINv" []]]);;

let COMPACT_IMP_COMPACT_IN_SUBTOPOLOGY = prove
 (`!top k s:A->bool.
     k compact_in top /\ k SUBSET s ==> k compact_in subtopology top s`,
   INTRO_TAC "!top k s; cpt sub" THEN
   ASM_SIMP_TAC[compact_in; TOPSPACE_SUBTOPOLOGY; SUBSET_INTER;
     COMPACT_IN_SUBSET_TOPSPACE] THEN
   INTRO_TAC "!U; open cover" THEN
   HYP_TAC "cpt: sub' cpt" (REWRITE_RULE[compact_in]) THEN
   (HYP_TAC "cpt: +" o SPEC)
     `{v:A->bool | v | open_in top v /\ ?u. u IN U /\ u = v INTER s}` THEN
   ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM] THEN TRANS_TAC SUBSET_TRANS `UNIONS U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC UNIONS_MONO THEN
    INTRO_TAC "![u]; u" THEN USE_THEN "u" (HYP_TAC "open" o C MATCH_MP) THEN
    HYP_TAC "open: @v. v ueq" (REWRITE_RULE[OPEN_IN_SUBTOPOLOGY]) THEN
    EXISTS_TAC `v:A->bool` THEN REMOVE_THEN "ueq" SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
    [EXISTS_TAC `v INTER s:A->bool` THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
   INTRO_TAC "@V. fin open cover" THEN
   EXISTS_TAC `{v INTER s | v | v:A->bool IN V}` THEN CONJ_TAC THENL
   [(SUBST1_TAC o SET_RULE)
      `{v INTER s | v | v:A->bool IN V} = IMAGE (\v. v INTER s) V` THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[GSYM INTER_UNIONS; SUBSET_INTER] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN INTRO_TAC "![u]; @v. v ueq" THEN
   REMOVE_THEN "ueq" SUBST_VAR_TAC THEN
   HYP_TAC "open" (REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   REMOVE_THEN "v" (HYP_TAC "open: v @u. u ueq" o C MATCH_MP) THEN
   REMOVE_THEN "ueq" SUBST_VAR_TAC THEN ASM_REWRITE_TAC[]);;

let COMPACT_IN_SUBTOPOLOGY_EQ = prove
 (`!top k s:A->bool.
     k compact_in subtopology top s <=> k compact_in top /\ k SUBSET s`,
  REPEAT GEN_TAC THEN
  CUT_TAC `k:A->bool compact_in subtopology top s ==> k SUBSET s` THENL
  [MESON_TAC[COMPACT_IMP_COMPACT_IN_SUBTOPOLOGY;
     COMPACT_IN_SUBTOPOLOGY_IMP_COMPACT];
   ALL_TAC] THEN
  DISCH_TAC THEN TRANS_TAC SUBSET_TRANS `topspace top INTER s:A->bool` THEN
  REWRITE_TAC[INTER_SUBSET] THEN
  ASM_SIMP_TAC[GSYM TOPSPACE_SUBTOPOLOGY; COMPACT_IN_SUBSET_TOPSPACE]);;

(* ------------------------------------------------------------------------- *)
(* Limits in a topological space.                                            *)
(* ------------------------------------------------------------------------- *)

let limit = new_definition
  `limit top (f:A->B) l net <=>
   l IN topspace top /\
   (!u. open_in top u /\ l IN u ==> eventually (\x. f x IN u) net)`;;

let LIMIT_IN_TOPSPACE = prove
 (`!net top f:A->B l. limit top f l net ==> l IN topspace top`,
  SIMP_TAC[limit]);;

let LIMIT_HAUSDORFF_UNIQUE = prove
 (`!net top f:A->B l1 l2.
     ~trivial_limit net /\
     (!x y. x IN topspace top /\
            y IN topspace top /\
            ~(x = y)
            ==> ?u v. open_in top u /\
                      open_in top v /\
                      x IN u /\
                      y IN v /\
                      DISJOINT u v) /\
     limit top f l1 net /\
     limit top f l2 net
     ==> l1 = l2`,
  REWRITE_TAC[limit] THEN INTRO_TAC "! *; nontriv hp (l1 hp1) (l2 hp2)" THEN
  REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "hp" (MP_TAC o SPECL [`l1:B`; `l2:B`]) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  CUT_TAC `open_in top u /\ open_in top v /\ l1:B IN u /\ l2:B IN v
           ==> ?x:A. f x IN u /\ f x IN v` THENL
  [SET_TAC[]; STRIP_TAC] THEN
  CLAIM_TAC "rmk" `eventually (\x:A. f x:B IN u /\ f x IN v) net` THENL
  [ASM_SIMP_TAC[EVENTUALLY_AND];
   HYP_TAC "rmk" (MATCH_MP EVENTUALLY_HAPPENS) THEN ASM_MESON_TAC[]]);;

let LIMIT_SEQUENTIALLY = prove
 (`!top s l:A.
     limit top s l sequentially <=>
     l IN topspace top /\
     (!u. open_in top u /\ l IN u ==> (?N. !n. N <= n ==> s n IN u))`,
  REWRITE_TAC[limit; EVENTUALLY_SEQUENTIALLY]);;

let LIMIT_SEQUENTIALLY_OFFSET = prove
 (`!top f l:A k. limit top f l sequentially
                 ==> limit top (\i. f (i + k)) l sequentially`,
  SIMP_TAC[LIMIT_SEQUENTIALLY] THEN INTRO_TAC "! *; l lim; !u; hp" THEN
  USE_THEN "hp" (HYP_TAC "lim: @N. N" o C MATCH_MP) THEN
  EXISTS_TAC `N:num` THEN INTRO_TAC "!n; n" THEN
  USE_THEN "N" MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let LIMIT_SEQUENTIALLY_OFFSET_REV = prove
 (`!top f l:A k. limit top (\i. f (i + k)) l sequentially
                 ==> limit top f l sequentially`,
  SIMP_TAC[LIMIT_SEQUENTIALLY] THEN INTRO_TAC "! *; l lim; !u; hp" THEN
  USE_THEN "hp" (HYP_TAC "lim: @N. N" o C MATCH_MP) THEN
  EXISTS_TAC `N+k:num` THEN INTRO_TAC "!n; n" THEN
  REMOVE_THEN "N" (MP_TAC o SPEC `n-k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n - k + k = n:num` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Topological limit in metric spaces.                                       *)
(* ------------------------------------------------------------------------- *)

let LIMIT_IN_MSPACE = prove
 (`!net m f:A->B l. limit (mtopology m) f l net ==> l IN mspace m`,
  MESON_TAC[LIMIT_IN_TOPSPACE; TOPSPACE_MTOPOLOGY]);;

let LIMIT_METRIC_UNIQUE = prove
 (`!m f:A->B l1 l2 net.
     ~trivial_limit net /\
     limit (mtopology m) f l1 net /\
     limit (mtopology m) f l2 net
     ==> l1 = l2`,
  REPEAT STRIP_TAC THEN
  (MATCH_MP_TAC o ISPECL [`net:(A)net`; `mtopology (m:B metric)`; `f:A->B`])
    LIMIT_HAUSDORFF_UNIQUE THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN INTRO_TAC "!x y; x y neq" THEN
  LABEL_ABBREV_TAC `r = mdist m (x:B,y) / &3` THEN
  MAP_EVERY EXISTS_TAC [`mball m (x:B,r)`; `mball m (y:B,r)`] THEN
  REMOVE_THEN "r" (SUBST_ALL_TAC o GSYM) THEN
  ASM_SIMP_TAC[OPEN_IN_MBALL; CENTRE_IN_MBALL; MDIST_POS_LT; REAL_LT_DIV;
    REAL_ARITH `&0 < &3`] THEN
  HYP SIMP_TAC "x y neq" [DISJOINT_MBALL; MDIST_POS_LT;
    REAL_ARITH `!x. &0 < x ==> x / &3 + x / &3 <= x`]);;

let LIMIT_METRIC = prove
 (`!m f:A->B l net.
     limit (mtopology m) f l net <=>
     l IN mspace m /\
     (!e. &0 < e
          ==> eventually (\x. f x IN mspace m /\ mdist m (f x, l) < e) net)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[limit; OPEN_IN_MTOPOLOGY; TOPSPACE_MTOPOLOGY] THEN EQ_TAC THENL
  [INTRO_TAC "l hp" THEN ASM_REWRITE_TAC[] THEN INTRO_TAC "!e; e" THEN
   REMOVE_THEN "hp" (MP_TAC o SPEC `mball m (l:B,e)`) THEN
   ASM_REWRITE_TAC[MBALL_SUBSET_MSPACE] THEN ASM_SIMP_TAC[CENTRE_IN_MBALL] THEN
   REWRITE_TAC[IN_MBALL] THEN ANTS_TAC THENL
   [INTRO_TAC "!x; x lt" THEN
    EXISTS_TAC `e - mdist m (l:B,x)` THEN
    CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     ASM_REWRITE_TAC[SUBSET; IN_MBALL] THEN INTRO_TAC "![y]; y lt'" THEN
     ASM_REWRITE_TAC[] THEN
     TRANS_TAC REAL_LET_TRANS `mdist m (l:B,x) + mdist m (x,y)` THEN
     ASM_SIMP_TAC[MDIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC (REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
    GEN_TAC THEN REWRITE_TAC[] THEN ASM_CASES_TAC `f (x:A):B IN mspace m` THEN
    ASM_SIMP_TAC[MDIST_SYM]];
   INTRO_TAC "l hp" THEN ASM_REWRITE_TAC[] THEN INTRO_TAC "!u; (u hp) l" THEN
   REMOVE_THEN "hp"
     (DESTRUCT_TAC "@r. r sub" o C MATCH_MP (ASSUME `l:B IN u`)) THEN
   REMOVE_THEN "hp" (MP_TAC o C MATCH_MP (ASSUME `&0 < r`)) THEN
   MATCH_MP_TAC (REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
   GEN_TAC THEN REWRITE_TAC[] THEN INTRO_TAC "f lt" THEN
   CLAIM_TAC "rmk" `f (x:A):B IN mball m (l,r)` THENL
   [ASM_SIMP_TAC[IN_MBALL; MDIST_SYM]; HYP SET_TAC "rmk sub" []]]);;

let LIMIT_METRIC_SEQUENTIALLY = prove
 (`!m f:num->A l.
     limit (mtopology m) f l sequentially <=>
     l IN mspace m /\
     (!e. &0 < e ==> (?N. !n. N <= n
                              ==> f n IN mspace m /\ mdist m (f n,l) < e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIMIT_METRIC; EVENTUALLY_SEQUENTIALLY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let LIMIT_IN_CLOSED_IN = prove
 (`!net top s f:A->B l.
      ~trivial_limit net /\ limit top f l net /\
      closed_in top s /\ eventually (\x. f x IN s) net
      ==> l IN s`,
  INTRO_TAC "! *; ntriv lim cl ev" THEN REFUTE_THEN (LABEL_TAC "contra") THEN
  HYP_TAC "lim: l lim" (REWRITE_RULE[limit]) THEN
  REMOVE_THEN "lim" (MP_TAC o SPEC `topspace top DIFF s:B->bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF; EVENTUALLY_AND] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN INTRO_TAC "nev" THEN
  HYP (MP_TAC o CONJ_LIST) "ev nev" [] THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN MATCH_MP_TAC NOT_EVENTUALLY THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let LIMIT_SUBMETRIC_IFF = prove
 (`!net m s f:A->B l.
     limit (mtopology (submetric m s)) f l net <=>
     l IN s /\ eventually (\x. f x IN s) net /\ limit (mtopology m) f l net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIMIT_METRIC; SUBMETRIC; IN_INTER; EVENTUALLY_AND] THEN
  EQ_TAC THEN SIMP_TAC[] THENL [INTRO_TAC "l hp"; MESON_TAC[]] THEN
  HYP_TAC "hp" (C MATCH_MP REAL_LT_01) THEN ASM_REWRITE_TAC[]);;

let METRIC_CLOSED_IN_IFF_SEQUENTIALLY_CLOSED = prove
 (`!m s:A->bool.
     closed_in (mtopology m) s <=>
     s SUBSET mspace m /\
     (!a l. (!n. a n IN s) /\ limit (mtopology m) a l sequentially
            ==> l IN s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "cl" THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_METRIC]; INTRO_TAC "!a l; a lim"] THEN
   MATCH_MP_TAC
     (ISPECL[`sequentially`; `mtopology (m:A metric)`] LIMIT_IN_CLOSED_IN) THEN
   EXISTS_TAC `a:num->A` THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE];
   ALL_TAC] THEN
  SIMP_TAC[CLOSED_IN_METRIC; IN_DIFF] THEN
  INTRO_TAC "sub seq; !x; x diff" THEN
  REFUTE_THEN (LABEL_TAC "contra" o
    REWRITE_RULE[NOT_EXISTS_THM; MESON[] `~(a /\ b) <=> a ==> ~b`]) THEN
  CLAIM_TAC "@a. a lt"
    `?a. (!n. a n:A IN s) /\ (!n. mdist m (x, a n) < inv(&n + &1))` THENL
  [REWRITE_TAC[GSYM FORALL_AND_THM; GSYM SKOLEM_THM] THEN GEN_TAC THEN
   REMOVE_THEN "contra" (MP_TAC o SPEC `inv (&n + &1)`) THEN
   ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[SET_RULE `~DISJOINT s t <=> ?x:A. x IN s /\ x IN t`] THEN
   ASM_REWRITE_TAC[IN_MBALL] THEN MESON_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "a'" `!n:num. a n:A IN mspace m` THENL
  [HYP SET_TAC "sub a" []; ALL_TAC] THEN
  REMOVE_THEN "seq" (MP_TAC o SPECL[`a:num->A`;`x:A`]) THEN
  ASM_REWRITE_TAC[LIMIT_METRIC_SEQUENTIALLY] THEN INTRO_TAC "!e; e" THEN
  HYP_TAC "e -> @N. NZ Ngt Nlt" (ONCE_REWRITE_RULE[REAL_ARCH_INV]) THEN
  EXISTS_TAC `N:num` THEN INTRO_TAC "!n; n" THEN
  TRANS_TAC REAL_LT_TRANS `inv (&n + &1)` THEN CONJ_TAC THENL
  [HYP MESON_TAC "lt a' x" [MDIST_SYM]; ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS `inv (&N)` THEN HYP REWRITE_TAC "Nlt" [] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Derived set (set of limit points).                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("derived_set_of",(21,"left"));;

let derived_set_of = new_definition
  `top derived_set_of s =
   {x:A | x IN topspace top /\
          (!t. x IN t /\ open_in top t
               ==> ?y. ~(y = x) /\ y IN s /\ y IN t)}`;;

let IN_DERIVED_SET_OF = prove
 (`!top s x:A.
     x IN top derived_set_of s <=>
     x IN topspace top /\
     (!t. x IN t /\ open_in top t ==> ?y. ~(y = x) /\ y IN s /\ y IN t)`,
  REWRITE_TAC[derived_set_of; IN_ELIM_THM]);;

let DERIVED_SET_OF_SUBSET_TOPSPACE = prove
 (`!top s:A->bool. top derived_set_of s SUBSET topspace top`,
  REWRITE_TAC[derived_set_of] THEN SET_TAC[]);;

let METRIC_DERIVED_SET_OF = prove
  (`!m s.
      mtopology m derived_set_of s =
      {x:A | x IN mspace m /\
            (!r. &0 < r ==> (?y. ~(y = x) /\ y IN s /\ y IN mball m (x,r)))}`,
  REWRITE_TAC[derived_set_of; TOPSPACE_MTOPOLOGY; OPEN_IN_MTOPOLOGY; EXTENSION;
              IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:A IN mspace m` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM (LABEL_TAC "x") THEN EQ_TAC THENL
  [INTRO_TAC "hp; !r; r" THEN HYP_TAC "hp: +" (SPEC `mball m (x:A,r)`) THEN
   ASM_REWRITE_TAC[CENTRE_IN_MBALL_EQ; MBALL_SUBSET_MSPACE] THEN
   DISCH_THEN MATCH_MP_TAC THEN HYP REWRITE_TAC "x" [IN_MBALL] THEN
   INTRO_TAC "![y]; y xy" THEN EXISTS_TAC `r - mdist m (x:A,y)` THEN
   CONJ_TAC THENL
   [REMOVE_THEN "xy" MP_TAC THEN REAL_ARITH_TAC;
    HYP REWRITE_TAC "x y" [SUBSET; IN_MBALL] THEN INTRO_TAC "![z]; z lt" THEN
    HYP REWRITE_TAC "z" [] THEN
    TRANS_TAC REAL_LET_TRANS `mdist m (x:A,y) + mdist m (y,z)` THEN
    ASM_SIMP_TAC[MDIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC];
   INTRO_TAC "hp; !t; t inc r" THEN
   HYP_TAC "r: @r. r ball" (C MATCH_MP (ASSUME `x:A IN t`)) THEN
   HYP_TAC "hp: @y. neq y dist" (C MATCH_MP (ASSUME `&0 < r`)) THEN
   EXISTS_TAC `y:A` THEN HYP REWRITE_TAC "neq y" [] THEN
   ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Closure with respect to a topological space.                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("closure_of",(21,"left"));;

let closure_of = new_definition
  `top closure_of s =
   {x:A | x IN topspace top /\
          (!t. x IN t /\ open_in top t ==> ?y. y IN s /\ y IN t)}`;;

let IN_CLOSURE_OF = prove
 (`!top s x:A.
     x IN top closure_of s <=>
     x IN topspace top /\
     (!t. x IN t /\ open_in top t ==> ?y. y IN s /\ y IN t)`,
  REWRITE_TAC[closure_of; IN_ELIM_THM]);;

let CLOSURE_OF_EMPTY = prove
 (`!top. top closure_of {}:A->bool = {}`,
  REWRITE_TAC[EXTENSION; IN_CLOSURE_OF; NOT_IN_EMPTY] THEN
  MESON_TAC[OPEN_IN_TOPSPACE]);;

let CLOSURE_OF_TOPSPACE = prove
 (`!top:A topology. top closure_of topspace top = topspace top`,
  REWRITE_TAC[EXTENSION; IN_CLOSURE_OF] THEN MESON_TAC[]);;

let CLOSURE_OF_UNIV = prove
 (`!top. top closure_of (:A) = topspace top`,
  REWRITE_TAC[closure_of] THEN SET_TAC[]);;

let CLOSURE_OF_SUBSET_TOPSPACE = prove
 (`!top s:A->bool. top closure_of s SUBSET topspace top`,
  REWRITE_TAC[closure_of] THEN SET_TAC[]);;

let METRIC_CLOSURE_OF = prove
  (`!m s.
      mtopology m closure_of s =
      {x:A | x IN mspace m /\
            (!r. &0 < r ==> (?y. y IN s /\ y IN mball m (x,r)))}`,
  REWRITE_TAC[closure_of; TOPSPACE_MTOPOLOGY; OPEN_IN_MTOPOLOGY; EXTENSION;
              IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:A IN mspace m` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM (LABEL_TAC "x") THEN EQ_TAC THENL
  [INTRO_TAC "hp; !r; r" THEN HYP_TAC "hp: +" (SPEC `mball m (x:A,r)`) THEN
   ASM_REWRITE_TAC[CENTRE_IN_MBALL_EQ; MBALL_SUBSET_MSPACE] THEN
   DISCH_THEN MATCH_MP_TAC THEN HYP REWRITE_TAC "x" [IN_MBALL] THEN
   INTRO_TAC "![y]; y xy" THEN EXISTS_TAC `r - mdist m (x:A,y)` THEN
   CONJ_TAC THENL
   [REMOVE_THEN "xy" MP_TAC THEN REAL_ARITH_TAC;
    HYP REWRITE_TAC "x y" [SUBSET; IN_MBALL] THEN INTRO_TAC "![z]; z lt" THEN
    HYP REWRITE_TAC "z" [] THEN
    TRANS_TAC REAL_LET_TRANS `mdist m (x:A,y) + mdist m (y,z)` THEN
    ASM_SIMP_TAC[MDIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC];
   INTRO_TAC "hp; !t; t inc r" THEN
   HYP_TAC "r: @r. r ball" (C MATCH_MP (ASSUME `x:A IN t`)) THEN
   HYP_TAC "hp: @y. y dist" (C MATCH_MP (ASSUME `&0 < r`)) THEN
   EXISTS_TAC `y:A` THEN HYP REWRITE_TAC "y" [] THEN
   ASM SET_TAC[]]);;

let CLOSURE_OF = prove
 (`!top s:A->bool.
     top closure_of s =
     topspace top INTER (s UNION top derived_set_of s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION] THEN FIX_TAC "[x]" THEN
  REWRITE_TAC[IN_CLOSURE_OF; IN_DERIVED_SET_OF; IN_UNION; IN_INTER] THEN
  ASM_CASES_TAC `x:A IN topspace top` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(LABEL_TAC "x_ok") THEN MESON_TAC[]);;

let DERIVED_SET_OF_SUBSET_CLOSURE_OF = prove
 (`!top s:A->bool. top derived_set_of s SUBSET top closure_of s`,
  REWRITE_TAC[CLOSURE_OF; SUBSET_INTER; DERIVED_SET_OF_SUBSET_TOPSPACE] THEN
  SIMP_TAC[SUBSET_UNION]);;

let DENSE_INTERSECTS_OPEN = prove
 (`!top s:A->bool.
     s SUBSET topspace top
     ==> (top closure_of s = topspace top <=>
          (!t. open_in top t /\ ~(t = {}) ==> ~(s INTER t = {})))`,
  INTRO_TAC "!top s; s" THEN EQ_TAC THENL
  [INTRO_TAC "dense; !t; t ne" THEN
   HYP_TAC "ne: @x0. x0" (REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
   CLAIM_TAC "1" `x0:A IN topspace top` THENL
   [CUT_TAC `t:A->bool SUBSET topspace top` THENL
    [HYP SET_TAC "x0" []; HYP SIMP_TAC "t" [OPEN_IN_SUBSET]];
    ALL_TAC] THEN
   CLAIM_TAC "2" `x0:A IN top closure_of s` THENL
   [HYP REWRITE_TAC "dense 1" []; ALL_TAC] THEN
   HYP_TAC "2: +" (REWRITE_RULE[IN_CLOSURE_OF]) THEN
   HYP REWRITE_TAC "1" [] THEN DISCH_THEN (MP_TAC o SPEC `t:A->bool`) THEN
   HYP REWRITE_TAC "x0 t" [] THEN SET_TAC[];
   INTRO_TAC "hp" THEN REWRITE_TAC[EXTENSION; IN_CLOSURE_OF] THEN
   GEN_TAC THEN ASM_CASES_TAC `x:A IN topspace top` THEN ASM_REWRITE_TAC[] THEN
   POP_ASSUM (LABEL_TAC "x") THEN INTRO_TAC "!t; x' t" THEN
   REMOVE_THEN "hp" (MP_TAC o SPEC `t:A->bool`) THEN
   HYP REWRITE_TAC "t" [] THEN HYP SET_TAC "x'" []]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy sequences and complete metric spaces.                              *)
(* ------------------------------------------------------------------------- *)

let cauchy_in = new_definition
  `!m:A metric s:num->A.
     cauchy_in m s <=>
     (!n. s n IN mspace m) /\
     (!e. &0 < e
          ==> (?N. !n n'. N <= n /\ N <= n'
                          ==> mdist m (s n,s n') < e))`;;

let mcomplete = new_definition
  `!m:A metric.
     mcomplete m <=>
     (!s. cauchy_in m s ==> ?x. limit (mtopology m) s x sequentially)`;;

let CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE = prove
 (`!m s:A->bool. closed_in (mtopology m) s /\ mcomplete m
                 ==> mcomplete (submetric m s)`,
  INTRO_TAC "!m s; cl cp" THEN REWRITE_TAC[mcomplete] THEN
  INTRO_TAC "![a]; a" THEN CLAIM_TAC "cy'" `cauchy_in m (a:num->A)` THENL
  [REMOVE_THEN "a" MP_TAC THEN SIMP_TAC[cauchy_in; SUBMETRIC; IN_INTER];
   HYP_TAC "cp" (GSYM o REWRITE_RULE[mcomplete]) THEN
   HYP REWRITE_TAC "cp" [LIMIT_SUBMETRIC_IFF] THEN
   REMOVE_THEN "cp" (HYP_TAC "cy': @l.l" o MATCH_MP) THEN EXISTS_TAC `l:A` THEN
   HYP_TAC "a: A cy" (REWRITE_RULE[cauchy_in; SUBMETRIC; IN_INTER]) THEN
   ASM_REWRITE_TAC[EVENTUALLY_TRUE] THEN MATCH_MP_TAC
     (ISPECL [`sequentially`; `mtopology(m:A metric)`] LIMIT_IN_CLOSED_IN) THEN
   EXISTS_TAC `a:num->A` THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE]]);;

let SEQUENTIALLY_CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE = prove
 (`!m s:A->bool.
     mcomplete m /\
     (!x l. (!n. x n IN s) /\ limit (mtopology m) x l sequentially ==> l IN s)
            ==> mcomplete (submetric m s)`,
  INTRO_TAC "!m s; cpl seq" THEN SUBGOAL_THEN
    `submetric m (s:A->bool) = submetric m (mspace m INTER s)` SUBST1_TAC THENL
  [REWRITE_TAC[submetric; INTER_ACI]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN
  ASM_REWRITE_TAC[METRIC_CLOSED_IN_IFF_SEQUENTIALLY_CLOSED; INTER_SUBSET] THEN
  INTRO_TAC "!a l; a lim" THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
  [MATCH_MP_TAC (ISPEC `sequentially` LIMIT_IN_MSPACE) THEN
   HYP MESON_TAC "lim" [];
   REMOVE_THEN "seq" MATCH_MP_TAC THEN HYP SET_TAC "a lim" []]);;

(* ------------------------------------------------------------------------- *)
(* Topological definition of continuous functions.                           *)
(* ------------------------------------------------------------------------- *)

let topcontinuous = new_definition
  `!top top' f:A->B.
     topcontinuous top top' f <=>
     (!x. x IN topspace top ==> f x IN topspace top') /\
     (!u. open_in top' u
          ==> open_in top {x | x IN topspace top /\ f x IN u})`;;

let TOPCONTINUOUS_IMAGE_SUBSET_TOPSPACE = prove
 (`!top top' f:A->B. topcontinuous top top' f
                     ==> IMAGE f (topspace top) SUBSET topspace top'`,
  REWRITE_TAC[topcontinuous] THEN SET_TAC[]);;

let TOPCONTINUOUS_LIMIT = prove
 (`!net top top' f:A->B g:B->C l.
     topcontinuous top top' g /\ limit top f l net
     ==> limit top' (g o f) (g l) net`,
  REWRITE_TAC[limit; o_THM] THEN INTRO_TAC "! *; cont l lim" THEN
  USE_THEN "cont" MP_TAC THEN REWRITE_TAC[topcontinuous] THEN
  INTRO_TAC "g cont" THEN ASM_SIMP_TAC[] THEN INTRO_TAC "!u; u gl" THEN
  ASM_CASES_TAC `trivial_limit (net:A net)` THENL
  [ASM_REWRITE_TAC[eventually]; POP_ASSUM (LABEL_TAC "nontriv")] THEN
  REMOVE_THEN "lim"
    (MP_TAC o SPEC `{x:B | x IN topspace top /\ g x:C IN u}`) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; eventually] THEN MESON_TAC[]);;

let TOPCONTINUOUS_IN_SUBTOPOLGY = prove
 (`!top top' s f:A->B.
     topcontinuous top (subtopology top' s) f <=>
     topcontinuous top top' f /\ IMAGE f (topspace top) SUBSET s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[topcontinuous; TOPSPACE_SUBTOPOLOGY; IN_INTER;
    OPEN_IN_SUBTOPOLOGY] THEN
  EQ_TAC THEN SIMP_TAC[] THENL
  [INTRO_TAC "img cont" THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
   INTRO_TAC "!u; u" THEN
   SUBGOAL_THEN
     `{x:A | x IN topspace top /\ f x:B IN u} =
      {x | x IN topspace top /\ f x IN u INTER s}`
     (fun th -> REWRITE_TAC[th]) THENL [HYP SET_TAC "img" []; ALL_TAC] THEN
   REMOVE_THEN "cont" MATCH_MP_TAC THEN EXISTS_TAC `u:B->bool` THEN
   ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
   INTRO_TAC "(img cont) img'" THEN
   CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   INTRO_TAC "!u; @t. t ueq" THEN REMOVE_THEN "ueq" SUBST_VAR_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN topspace top /\ f x:B IN t INTER s} =
      {x | x IN topspace top /\ f x IN t}`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   ASM SET_TAC[]]);;

let IMAGE_COMPACT_IN = prove
 (`!top top' (f:A->B) s.
     s compact_in top /\ topcontinuous top top' f
     ==> (IMAGE f s) compact_in top'`,
  INTRO_TAC "!top top' f s; cpt cont" THEN REWRITE_TAC[compact_in] THEN
  CONJ_TAC THENL
  [TRANS_TAC SUBSET_TRANS `IMAGE (f:A->B) (topspace top)` THEN
   ASM_SIMP_TAC[TOPCONTINUOUS_IMAGE_SUBSET_TOPSPACE; IMAGE_SUBSET;
     COMPACT_IN_SUBSET_TOPSPACE];
   INTRO_TAC "!U; U img"] THEN
  HYP_TAC "cpt : sub cpt" (REWRITE_RULE[compact_in]) THEN
  REMOVE_THEN "cpt" (MP_TAC o
    SPEC `{{x | x | x IN topspace top /\ (f:A->B) x IN u} | u | u IN U}`) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
   INTRO_TAC "{![w]; @v. v eq & !x; x}" THENL
   [REMOVE_THEN "eq" SUBST1_TAC THEN
    HYP_TAC "cont : wd cont" (REWRITE_RULE[topcontinuous]) THEN ASM SET_TAC[];
    REMOVE_THEN "img" (MP_TAC o SPEC `f (x:A):B` o REWRITE_RULE[SUBSET]) THEN
    ANTS_TAC THENL [HYP SET_TAC "x" []; REWRITE_TAC[IN_UNIONS]] THEN
    INTRO_TAC "@t. t fx" THEN
    EXISTS_TAC `{x:A | x IN topspace top /\ f x:B IN t}` THEN ASM SET_TAC[]];
   ALL_TAC] THEN
  INTRO_TAC "@V. fin sub s" THEN
  CLAIM_TAC "@u. u"
    `?u. !v. v IN V ==> u v IN U /\
                        v = {x:A | x IN topspace top /\ f x:B IN u v}` THENL
  [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
   INTRO_TAC "!v; v" THEN
   HYP_TAC "sub" (REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   REMOVE_THEN "v" (HYP_TAC "sub: @u. u eq" o C MATCH_MP) THEN
   EXISTS_TAC `u:B->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  EXISTS_TAC `IMAGE (u:(A->bool)->(B->bool)) V` THEN CONJ_TAC THENL
  [HYP SIMP_TAC "fin" [FINITE_IMAGE]; ASM SET_TAC []]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise continuity in topological spaces.                               *)
(* ------------------------------------------------------------------------- *)

let topcontinuous_at = new_definition
  `!top top' f:A->B x.
     topcontinuous_at top top' f x <=>
     x IN topspace top /\
     (!x. x IN topspace top ==> f x IN topspace top') /\
     (!v. open_in top' v /\ f x IN v
          ==> (?u. open_in top u /\ x IN u /\ (!y. y IN u ==> f y IN v)))`;;

let TOPCONTINUOUS_EQ_TOPCONTINUOUS_AT = prove
 (`!top top' f:A->B.
     topcontinuous top top' f <=>
     (!x. x IN topspace top ==> topcontinuous_at top top' f x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [SIMP_TAC[topcontinuous; topcontinuous_at] THEN
   INTRO_TAC "f v; !x; x; !v; v1 v2" THEN
   REMOVE_THEN "v" (MP_TAC o C MATCH_MP
     (ASSUME `open_in top' (v:B->bool)`)) THEN
   INTRO_TAC "pre" THEN
   EXISTS_TAC `{x:A | x IN topspace top /\ f x:B IN v}` THEN
   ASM_SIMP_TAC[IN_ELIM_THM];
   ALL_TAC] THEN
  SIMP_TAC[topcontinuous; topcontinuous_at; SUBSET] THEN
  INTRO_TAC "hp1" THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  INTRO_TAC "![v]; v" THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN INTRO_TAC "!x; x1 x2" THEN
  REMOVE_THEN "hp1" (MP_TAC o SPEC `x:A`) THEN ASM_SIMP_TAC[] THEN
  INTRO_TAC "x3 v1" THEN REMOVE_THEN "v1" (MP_TAC o SPEC `v:B->bool`) THEN
  USE_THEN "x1" (LABEL_TAC "x4" o REWRITE_RULE[IN_ELIM_THM]) THEN
  ASM_SIMP_TAC[] THEN INTRO_TAC "@u. u1 u2 u3" THEN
  EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Continuous functions on metric spaces.                                    *)
(* ------------------------------------------------------------------------- *)

let METRIC_TOPCONTINUOUS = prove
 (`!m m' f:A->B.
     topcontinuous (mtopology m) (mtopology m') f <=>
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!a e. &0 < e /\ a IN mspace m
            ==> (?d. &0 < d /\
                     (!x. x IN mspace m /\ mdist m (a,x) < d
                          ==> mdist m' (f a, f x) < e)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[topcontinuous; TOPSPACE_MTOPOLOGY] THEN
  EQ_TAC THEN SIMP_TAC[] THENL
  [INTRO_TAC "f cont; !a e; e a" THEN
   REMOVE_THEN "cont" (MP_TAC o SPEC `mball m' (f (a:A):B,e)`) THEN
   REWRITE_TAC[OPEN_IN_MBALL] THEN
   ASM_SIMP_TAC[OPEN_IN_MTOPOLOGY; SUBSET; IN_MBALL; IN_ELIM_THM] THEN
   DISCH_THEN (MP_TAC o SPEC `a:A`) THEN ASM_SIMP_TAC[MDIST_REFL];
   SIMP_TAC[OPEN_IN_MTOPOLOGY; SUBSET; IN_MBALL; IN_ELIM_THM] THEN
   ASM_MESON_TAC[]]);;

let TOPCONTINUOUS_TO_METRIC = prove
 (`!t m f:A->B.
     topcontinuous t (mtopology m) f <=>
     (!x. x IN topspace t
          ==> (!r. &0 < r
                   ==> (?u. open_in t u /\
                            x IN u /\
                            (!y. y IN u ==> f y IN mball m (f x,r)))))`,
  INTRO_TAC "!t m f" THEN
  REWRITE_TAC[TOPCONTINUOUS_EQ_TOPCONTINUOUS_AT; topcontinuous_at;
              TOPSPACE_MTOPOLOGY] THEN
  EQ_TAC THENL
  [INTRO_TAC "A; !x; x" THEN REMOVE_THEN "A" (MP_TAC o SPEC `x:A`) THEN
   ASM_SIMP_TAC[OPEN_IN_MBALL; CENTRE_IN_MBALL];
   INTRO_TAC "A; !x; x" THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_01; IN_MBALL];
    ASM_MESON_TAC[OPEN_IN_MTOPOLOGY; SUBSET]]]);;

(* ------------------------------------------------------------------------- *)
(* Lipschitz functions.                                                      *)
(* ------------------------------------------------------------------------- *)

let LIPSCHITZ_COEFFICIENT_POS = prove
 (`!m m' f:A->B k.
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m' (f x,f y) <= k * mdist m (x,y)) /\
     (?x y. x IN mspace m /\ y IN mspace m /\ ~(f x = f y))
     ==> &0 < k`,
  REPEAT GEN_TAC THEN INTRO_TAC "f k (@x y. x y fneq)" THEN
  CLAIM_TAC "neq" `~(x:A = y)` THENL [HYP MESON_TAC "fneq" []; ALL_TAC] THEN
  TRANS_TAC REAL_LTE_TRANS `mdist m' (f x:B,f y) / mdist m (x:A,y)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; MDIST_POS_LT; REAL_LE_LDIV_EQ]);;

let LIPSCHITZ_CONTINUOUS_IMP_TOPCONTINUOUS = prove
 (`!m m' (f:A->B) k.
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m' (f x,f y) <= k * mdist m (x,y))
     ==> topcontinuous (mtopology m) (mtopology m') f`,
  SIMP_TAC[METRIC_TOPCONTINUOUS] THEN INTRO_TAC "! *; f lip; !a e; e a" THEN
  ASM_CASES_TAC `?y:A. y IN mspace m /\ ~(f a:B = f y)` THENL
  [EXISTS_TAC `e / k` THEN POP_ASSUM (DESTRUCT_TAC "@y. y neq") THEN
   CLAIM_TAC "kpos" `&0 < k` THENL
   [(MATCH_MP_TAC o ISPECL[`m:A metric`; `m':B metric`; `f:A->B`])
      LIPSCHITZ_COEFFICIENT_POS THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[REAL_LT_DIV] THEN INTRO_TAC "!x; x lt" THEN
    TRANS_TAC REAL_LET_TRANS `k * mdist m (a:A,x)` THEN ASM_SIMP_TAC[] THEN
    REMOVE_THEN "lt" MP_TAC THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_SYM]];
   POP_ASSUM
     (LABEL_TAC "eq" o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
   EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
   INTRO_TAC "![y]; y d" THEN REMOVE_THEN "eq" (MP_TAC o SPEC `y:A`) THEN
   ASM_SIMP_TAC[MDIST_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Contractions.                                                             *)
(* ------------------------------------------------------------------------- *)

let CONTRACTION_IMP_UNIQUE_FIXPOINT = prove
 (`!m (f:A->A) k x y.
     k < &1 /\
     (!x. x IN mspace m ==> f x IN mspace m) /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m (f x, f y) <= k * mdist m (x,y)) /\
     x IN mspace m /\ y IN mspace m /\ f x = x /\ f y = y
     ==> x = y`,
  INTRO_TAC "!m f k x y; k f le x y xeq yeq" THEN
  ASM_CASES_TAC `x:A = y` THENL [POP_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REMOVE_THEN "le" (MP_TAC o SPECL[`x:A`;`y:A`]) THEN ASM_REWRITE_TAC[] THEN
  CUT_TAC `&0 < (&1 - k) * mdist m (x:A,y:A)` THENL
  [REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[MDIST_POS_LT] THEN
   ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Banach Fixed-Point Theorem (aka, Contraction Mapping Principle).          *)
(* ------------------------------------------------------------------------- *)

let BANACH_FIXPOINT_THM = prove
 (`!m f:A->A k.
     ~(mspace m = {}) /\
     mcomplete m /\
     (!x. x IN mspace m ==> f x IN mspace m) /\
     k < &1 /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m (f x, f y) <= k * mdist m (x,y))
     ==> (?!x. x IN mspace m /\ f x = x)`,
  INTRO_TAC "!m f k; ne compl 4 k1 contr" THEN REMOVE_THEN "ne" MP_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN INTRO_TAC "@a. aINm" THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
  [ALL_TAC;
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTRACTION_IMP_UNIQUE_FIXPOINT THEN
   ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `!x:A. x IN mspace m ==> f x:A = f a` THENL
  [ASM_MESON_TAC[]; POP_ASSUM (LABEL_TAC "nonsing")] THEN
  CLAIM_TAC "kpos" `&0 < k` THENL
  [MATCH_MP_TAC (ISPECL [`m:A metric`; `m:A metric`; `f:A->A`]
     LIPSCHITZ_COEFFICIENT_POS) THEN
   ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "fINm" `!n:num. (ITER n f (a:A)) IN mspace m` THENL
  [LABEL_INDUCT_TAC THEN ASM_SIMP_TAC[ITER]; ALL_TAC] THEN
  ASM_CASES_TAC `f a = a:A` THENL
  [ASM_MESON_TAC[]; POP_ASSUM (LABEL_TAC "aneq")] THEN
  CUT_TAC `cauchy_in (m:A metric) (\n. ITER n f (a:A))` THENL
  [DISCH_THEN (fun cauchy -> HYP_TAC "compl : @l. lim"
    (C MATCH_MP cauchy o REWRITE_RULE[mcomplete])) THEN
   EXISTS_TAC `l:A` THEN CONJ_TAC THENL
   [ASM_MESON_TAC [LIMIT_IN_MSPACE]; ALL_TAC] THEN
   MATCH_MP_TAC
     (ISPECL [`m:A metric`; `(\n. ITER n f a:A)`] LIMIT_METRIC_UNIQUE) THEN
   EXISTS_TAC `sequentially` THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   MATCH_MP_TAC LIMIT_SEQUENTIALLY_OFFSET_REV THEN
   EXISTS_TAC `1` THEN REWRITE_TAC[GSYM ADD1] THEN
   SUBGOAL_THEN `(\i. ITER (SUC i) f (a:A)) = f o (\i. ITER i f a)`
     SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; ITER]; ALL_TAC] THEN
   MATCH_MP_TAC TOPCONTINUOUS_LIMIT THEN
   EXISTS_TAC `mtopology (m:A metric)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_IMP_TOPCONTINUOUS THEN
   EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "k1'" `&0 < &1 - k` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[cauchy_in] THEN INTRO_TAC "!e; e" THEN
  CLAIM_TAC "@N. N" `?N. k pow N < ((&1 - k) * e) / mdist m (a:A,f a)` THENL
  [MATCH_MP_TAC REAL_ARCH_POW_INV THEN
   ASM_SIMP_TAC[REAL_LT_DIV; MDIST_POS_LT; REAL_LT_MUL];
   EXISTS_TAC `N:num`] THEN
  MATCH_MP_TAC WLOG_LT THEN ASM_SIMP_TAC[MDIST_REFL] THEN CONJ_TAC THENL
  [HYP MESON_TAC "fINm" [MDIST_SYM]; ALL_TAC] THEN
  INTRO_TAC "!n n'; lt; le le'" THEN
  TRANS_TAC REAL_LET_TRANS
    `sum (n..n'-1) (\i. mdist m (ITER i f a:A, ITER (SUC i) f a))` THEN
  CONJ_TAC THENL
  [REMOVE_THEN "lt" MP_TAC THEN SPEC_TAC (`n':num`,`n':num`) THEN
   LABEL_INDUCT_TAC THENL [REWRITE_TAC[LT]; REWRITE_TAC[LT_SUC_LE]] THEN
   INTRO_TAC "nle" THEN HYP_TAC "nle : nlt | neq" (REWRITE_RULE[LE_LT]) THENL
   [ALL_TAC;
    POP_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[ITER;
      ARITH_RULE `SUC n'' - 1 = n''`; SUM_SING_NUMSEG; REAL_LE_REFL]] THEN
   USE_THEN "nlt" (HYP_TAC "ind_n'" o C MATCH_MP) THEN REWRITE_TAC[ITER] THEN
   TRANS_TAC REAL_LE_TRANS
     `mdist m (ITER n f a:A,ITER n'' f a) +
      mdist m (ITER n'' f a,f (ITER n'' f a))` THEN
   ASM_SIMP_TAC[MDIST_TRIANGLE] THEN
   SUBGOAL_THEN `SUC n'' - 1 = SUC (n'' - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG]] THEN
   SUBGOAL_THEN `SUC (n'' - 1) = n''` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[LT_IMP_LE; REAL_LE_RADD]] THEN
   REMOVE_THEN "ind_n'" (ACCEPT_TAC o REWRITE_RULE[ITER]);
   ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
     `sum (n..n'-1) (\i. mdist m (a:A, f a) * k pow i)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC SUM_LE_NUMSEG THEN
   CUT_TAC `!i. mdist m (ITER i f a,ITER (SUC i) f a) <=
                mdist m (a:A,f a) * k pow i` THENL
   [SIMP_TAC[ITER]; ALL_TAC] THEN
   LABEL_INDUCT_TAC THENL
   [REWRITE_TAC[ITER; real_pow; REAL_MUL_RID; REAL_LE_REFL];
    HYP_TAC "ind_i" (REWRITE_RULE[ITER]) THEN
    TRANS_TAC REAL_LE_TRANS `k * mdist m (ITER i f a:A, f (ITER i f a))` THEN
    ASM_SIMP_TAC[real_pow; REAL_LE_LMUL_EQ; ITER;
      REAL_ARITH `!x. x * k * k pow i = k * x * k pow i`]];
   ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; SUM_GP] THEN
  HYP SIMP_TAC "lt" [ARITH_RULE `n < n' ==> ~(n' - 1 < n)`] THEN
  HYP SIMP_TAC "k1" [REAL_ARITH `k < &1 ==> ~(k = &1)`] THEN
  USE_THEN "lt" (SUBST1_TAC o
    MATCH_MP (ARITH_RULE `n < n' ==> SUC (n' - 1) = n'`)) THEN
  SUBGOAL_THEN `k pow n - k pow n' = k pow n * (&1 - k pow (n' - n))`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID; GSYM REAL_POW_ADD] THEN
   HYP SIMP_TAC "lt" [ARITH_RULE `n < n' ==> n + n' - n = n':num`];
   (SUBST1_TAC o REAL_ARITH)
     `mdist m (a:A,f a) * (k pow n * (&1 - k pow (n' - n))) / (&1 - k) =
      ((k pow n * (&1 - k pow (n' - n))) / (&1 - k)) * mdist m (a,f a)`] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; MDIST_POS_LT; REAL_LT_LDIV_EQ] THEN
  TRANS_TAC REAL_LET_TRANS `k pow n` THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
   REWRITE_TAC[GSYM REAL_POW_ADD;
     REAL_ARITH `k pow n - k pow n * (&1 - k pow (n' - n)) =
                 k pow n * k pow (n' - n)`] THEN
   HYP SIMP_TAC "lt" [ARITH_RULE `n < n' ==> n + n' - n = n':num`] THEN
   HYP SIMP_TAC "kpos" [REAL_POW_LE; REAL_LT_IMP_LE];
   TRANS_TAC REAL_LET_TRANS `k pow N` THEN
   ASM_SIMP_TAC[REAL_POW_MONO_INV; REAL_LT_IMP_LE;
     REAL_ARITH `e / mdist m (a:A,f a) * (&1 - k) =
                 ((&1 - k) * e) / mdist m (a,f a)`]]);;

(* ------------------------------------------------------------------------- *)
(* Metric space of bounded functions.                                        *)
(* ------------------------------------------------------------------------- *)

let funspace = new_definition
  `funspace s m =
   metric ({f:A->B | (!x. x IN s ==> f x IN mspace m) /\
                     f IN EXTENSIONAL s /\
                     mbounded m (IMAGE f s)},
           (\(f,g). if s = {} then &0 else
                    sup {mdist m (f x,g x) | x | x IN s}))`;;

let FUNSPACE = (REWRITE_RULE[GSYM FORALL_AND_THM] o prove)
 (`!s m.
     mspace (funspace s m) =
       {f:A->B | (!x. x IN s ==> f x IN mspace m) /\
                 f IN EXTENSIONAL s /\
                 mbounded m (IMAGE f s)} /\
     (!f g. mdist (funspace s m) (f,g) =
              if s = {} then &0 else
              sup {mdist m (f x,g x) | x | x IN s})`,
  REPEAT GEN_TAC THEN MAP_EVERY LABEL_ABBREV_TAC
    [`fspace = {f:A->B | (!x. x IN s ==> f x IN mspace m) /\
                         f IN EXTENSIONAL s /\
                         mbounded m (IMAGE f s)}`;
     `fdist =
        \(f,g). if s = {} then &0 else
                sup {mdist m (f x:B,g x) | x | x:A IN s}`] THEN
  CUT_TAC `mspace (funspace s m) = fspace:(A->B)->bool /\
           mdist (funspace s m:(A->B)metric) = fdist` THENL
  [EXPAND_TAC "fdist" THEN DISCH_THEN (fun th -> REWRITE_TAC[th]);
   ASM_REWRITE_TAC[funspace] THEN MATCH_MP_TAC METRIC] THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
  [POP_ASSUM SUBST_ALL_TAC THEN MAP_EVERY EXPAND_TAC ["fspace"; "fdist"] THEN
   SIMP_TAC[is_metric_space; NOT_IN_EMPTY; IN_EXTENSIONAL; IMAGE_CLAUSES;
     MBOUNDED_EMPTY; IN_ELIM_THM; REAL_LE_REFL; REAL_ADD_LID; FUN_EQ_THM];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  REMOVE_THEN "nempty" (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN LABEL_TAC "nempty" th) THEN
  CLAIM_TAC "wd ext bound"
    `(!f x:A. f IN fspace /\ x IN s ==> f x:B IN mspace m) /\
     (!f. f IN fspace ==> f IN EXTENSIONAL s) /\
     (!f. f IN fspace
          ==> (?c b. c IN mspace m /\
                     (!x. x IN s ==> mdist m (c,f x) <= b)))` THENL
  [EXPAND_TAC "fspace" THEN
   ASM_SIMP_TAC[IN_ELIM_THM; MBOUNDED; IMAGE_EQ_EMPTY] THEN SET_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "bound2"
    `!f g:A->B. f IN fspace /\ g IN fspace
                ==> (?b. !x. x IN s ==> mdist m (f x,g x) <= b)` THENL
  [REMOVE_THEN "fspace" (SUBST_ALL_TAC o GSYM) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   CUT_TAC `mbounded m (IMAGE (f:A->B) s UNION IMAGE g s)` THENL
   [REWRITE_TAC[MBOUNDED_IFF_FINITE_DIAMETER; SUBSET; IN_UNION] THEN
    STRIP_TAC THEN EXISTS_TAC `b:real` THEN ASM SET_TAC [];
    ASM_REWRITE_TAC[MBOUNDED_UNION]];
   ALL_TAC] THEN
  HYP_TAC "nempty -> @a. a" (REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[is_metric_space] THEN CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f  g" THEN EXPAND_TAC "fdist" THEN
   REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_SUP THEN
   CLAIM_TAC "@b. b" `?b. !x:A. x IN s ==> mdist m (f x:B,g x) <= b` THENL
   [HYP SIMP_TAC "bound2 f g" [];
    ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `mdist m (f(a:A):B,g a)`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN HYP SIMP_TAC "wd f g a" [MDIST_POS_LE] THEN
    HYP MESON_TAC "a b" [];
    ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f  g" THEN EXPAND_TAC "fdist" THEN
   REWRITE_TAC[] THEN EQ_TAC THENL
   [INTRO_TAC "sup0" THEN MATCH_MP_TAC (SPEC `s:A->bool` EXTENSIONAL_EQ) THEN
    HYP SIMP_TAC "f g ext" [] THEN INTRO_TAC "!x; x" THEN
    REFUTE_THEN (LABEL_TAC "neq") THEN
    CUT_TAC
      `&0 < mdist m (f (x:A):B, g x) /\
       mdist m (f x, g x) <= sup {mdist m (f x,g x) | x IN s}` THENL
    [HYP REWRITE_TAC "sup0" [] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    HYP SIMP_TAC "wd f g x neq" [MDIST_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_SUP THEN
    CLAIM_TAC "@B. B" `?b. !x:A. x IN s ==> mdist m (f x:B,g x) <= b` THENL
    [HYP SIMP_TAC "bound2 f g" []; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `mdist m (f (x:A):B,g x)`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN
    HYP MESON_TAC "B x" [];
    DISCH_THEN (SUBST1_TAC o GSYM) THEN
    SUBGOAL_THEN `{mdist m (f x:B,f x) | x:A IN s} = {&0}`
      (fun th -> REWRITE_TAC[th; SUP_SING]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV; IN_INSERT] THEN
    HYP MESON_TAC "wd f a" [MDIST_REFL]];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f g" THEN EXPAND_TAC "fdist" THEN REWRITE_TAC[] THEN
   AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   HYP MESON_TAC "wd f g" [MDIST_SYM];
   ALL_TAC] THEN
  INTRO_TAC "![f] [g] [h]; f g h" THEN EXPAND_TAC "fdist" THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV] THEN
   HYP MESON_TAC "a" [];
   ALL_TAC] THEN
  FIX_TAC "[d]" THEN REWRITE_TAC [IN_ELIM_THM; IN_UNIV] THEN
  INTRO_TAC "@x. x d" THEN POP_ASSUM SUBST1_TAC THEN
  CUT_TAC
    `mdist m (f (x:A):B,h x) <= mdist m (f x,g x) + mdist m (g x, h x) /\
     mdist m (f x, g x) <= fdist (f,g) /\
     mdist m (g x, h x) <= fdist (g,h)` THEN
  EXPAND_TAC "fdist" THEN REWRITE_TAC[] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  HYP SIMP_TAC "wd f g h x" [MDIST_TRIANGLE] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_SUP THENL
  [CLAIM_TAC "@B. B" `?b. !x:A. x IN s ==> mdist m (f x:B,g x) <= b` THENL
   [HYP SIMP_TAC "bound2 f g" [];
    MAP_EVERY EXISTS_TAC [`B:real`; `mdist m (f(x:A):B,g x)`]] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN HYP MESON_TAC "B x" [];
   CLAIM_TAC "@B. B" `?b. !x:A. x IN s ==> mdist m (g x:B,h x) <= b` THENL
   [HYP SIMP_TAC "bound2 g h" []; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`B:real`; `mdist m (g(x:A):B,h x)`] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN
   HYP MESON_TAC "B x" []]);;

let FUNSPACE_IMP_WELLDEFINED = prove
 (`!s m f:A->B x. f IN mspace (funspace s m) /\ x IN s ==> f x IN mspace m`,
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

let FUNSPACE_IMP_EXTENSIONAL = prove
 (`!s m f:A->B. f IN mspace (funspace s m) ==> f IN EXTENSIONAL s`,
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

let FUNSPACE_IMP_BOUNDED_IMAGE = prove
 (`!s m f:A->B. f IN mspace (funspace s m) ==> mbounded m (IMAGE f s)`,
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

let FUNSPACE_IMP_BOUNDED = prove
 (`!s m f:A->B. f IN mspace (funspace s m)
                ==> s = {} \/ (?c b. !x. x IN s ==> mdist m (c,f x) <= b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FUNSPACE; MBOUNDED; IMAGE_EQ_EMPTY; IN_ELIM_THM] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let FUNSPACE_IMP_BOUNDED2 = prove
 (`!s m f g:A->B. f IN mspace (funspace s m) /\ g IN mspace (funspace s m)
                  ==> (?b. !x. x IN s ==> mdist m (f x,g x) <= b)`,
  REWRITE_TAC[FUNSPACE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  CUT_TAC `mbounded m (IMAGE (f:A->B) s UNION IMAGE g s)` THENL
  [REWRITE_TAC[MBOUNDED_IFF_FINITE_DIAMETER; SUBSET; IN_UNION] THEN
   STRIP_TAC THEN EXISTS_TAC `b:real` THEN ASM SET_TAC [];
   ASM_REWRITE_TAC[MBOUNDED_UNION]]);;

let FUNSPACE_MDIST_LE = prove
 (`!s m f g:A->B a.
     ~(s = {}) /\
     f IN mspace (funspace s m) /\
     g IN mspace (funspace s m)
     ==> (mdist (funspace s m) (f,g) <= a <=>
          !x. x IN s ==> mdist m (f x, g x) <= a)`,
  INTRO_TAC "! *; ne f g" THEN
  HYP (DESTRUCT_TAC "@b. b" o
    MATCH_MP FUNSPACE_IMP_BOUNDED2 o CONJ_LIST) "f g" [] THEN
  ASM_REWRITE_TAC[FUNSPACE] THEN
  MP_TAC (ISPECL [`{mdist m (f x:B,g x) | x:A IN s}`; `a:real`]
    REAL_SUP_LE_EQ) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM]] THEN
  MESON_TAC[]);;

let MCOMPLETE_FUNSPACE = prove
 (`!s:A->bool m:B metric. mcomplete m ==> mcomplete (funspace s m)`,
  REWRITE_TAC[mcomplete] THEN INTRO_TAC "!s m; cpl; ![f]; cy" THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
  [POP_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `\x:A. UNDEFINED:B` THEN
   REMOVE_THEN "cy" MP_TAC THEN
   SIMP_TAC[cauchy_in; LIMIT_METRIC_SEQUENTIALLY; FUNSPACE; NOT_IN_EMPTY;
     IN_ELIM_THM; IN_EXTENSIONAL; IMAGE_CLAUSES; MBOUNDED_EMPTY];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  LABEL_ABBREV_TAC
    `g (x:A) = if x IN s
               then @y. limit (mtopology m) (\n:num. f n x) y sequentially
               else UNDEFINED:B` THEN
  EXISTS_TAC `g:A->B` THEN USE_THEN "cy" MP_TAC THEN
  HYP REWRITE_TAC "nempty"
    [cauchy_in; FUNSPACE; IN_ELIM_THM; FORALL_AND_THM] THEN
  INTRO_TAC "(fwd fext fbd) cy'" THEN
  ASM_REWRITE_TAC[LIMIT_METRIC_SEQUENTIALLY; FUNSPACE; IN_ELIM_THM] THEN
  CLAIM_TAC "gext" `g:A->B IN EXTENSIONAL s` THENL
  [REMOVE_THEN "g" (fun th -> SIMP_TAC[IN_EXTENSIONAL; GSYM th]);
   HYP REWRITE_TAC "gext" []] THEN
  CLAIM_TAC "bd2"
     `!n n'. ?b. !x:A. x IN s ==> mdist m (f (n:num) x:B, f n' x) <= b` THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC FUNSPACE_IMP_BOUNDED2 THEN
   ASM_REWRITE_TAC[FUNSPACE; IN_ELIM_THM; ETA_AX];
   ALL_TAC] THEN
  CLAIM_TAC "sup"
    `!n n':num x0:A. x0 IN s
                     ==> mdist m (f n x0:B,f n' x0) <=
                         sup {mdist m (f n x,f n' x) | x IN s}` THENL
  [INTRO_TAC "!n n' x0; x0" THEN MATCH_MP_TAC REAL_LE_SUP THEN
   REMOVE_THEN "bd2" (DESTRUCT_TAC "@b. b" o SPECL[`n:num`;`n':num`]) THEN
   MAP_EVERY EXISTS_TAC
     [`b:real`; `mdist m (f (n:num) (x0:A):B, f n' x0)`] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [HYP MESON_TAC "x0" []; REWRITE_TAC[REAL_LE_REFL]] THEN
   INTRO_TAC "![d]; @y. y d" THEN REMOVE_THEN "d" SUBST1_TAC THEN
   HYP SIMP_TAC "b y" [];
   ALL_TAC] THEN
  CLAIM_TAC "pcy" `!x:A. x IN s ==> cauchy_in m (\n. f n x:B)` THENL
  [INTRO_TAC "!x; x" THEN REWRITE_TAC[cauchy_in] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "!e; e" THEN
   USE_THEN "e" (HYP_TAC "cy': @N.N" o C MATCH_MP) THEN EXISTS_TAC `N:num` THEN
   REPEAT GEN_TAC THEN DISCH_THEN (HYP_TAC "N" o C MATCH_MP) THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {mdist m (f (n:num) x:B,f n' x) | x:A IN s}` THEN
   HYP REWRITE_TAC "N" [] THEN HYP SIMP_TAC "sup x" [];
   ALL_TAC] THEN
  CLAIM_TAC "glim"
    `!x:A. x IN s
           ==> limit (mtopology m) (\n. f n x:B) (g x) sequentially` THENL
  [INTRO_TAC "!x; x" THEN
   REMOVE_THEN "g" (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
   SELECT_ELIM_TAC THEN HYP SIMP_TAC "cpl pcy x" [];
   ALL_TAC] THEN
  CLAIM_TAC "gwd" `!x:A. x IN s ==> g x:B IN mspace m` THENL
  [INTRO_TAC "!x; x" THEN
   MATCH_MP_TAC (ISPECL[`sequentially`] LIMIT_IN_MSPACE) THEN
   EXISTS_TAC `\n:num. f n (x:A):B` THEN HYP SIMP_TAC "glim x" [];
   HYP REWRITE_TAC "gwd" []] THEN
  CLAIM_TAC "unif"
    `!e. &0 < e ==> ?N:num. !x:A n. x IN s /\ N <= n
                    ==> mdist m (f n x:B, g x) < e` THENL
  [INTRO_TAC "!e; e" THEN REMOVE_THEN "cy'" (MP_TAC o SPEC `e / &2`) THEN
   HYP REWRITE_TAC "e" [REAL_HALF] THEN INTRO_TAC "@N. N" THEN
   EXISTS_TAC `N:num` THEN INTRO_TAC "!x n; x n" THEN
   USE_THEN "x" (HYP_TAC "glim" o C MATCH_MP) THEN
   HYP_TAC "glim: gx glim" (REWRITE_RULE[LIMIT_METRIC_SEQUENTIALLY]) THEN
   REMOVE_THEN "glim" (MP_TAC o SPEC `e / &2`) THEN
   HYP REWRITE_TAC "e" [REAL_HALF] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "@N'. N'" THEN
   TRANS_TAC REAL_LET_TRANS
     `mdist m (f n (x:A):B, f (MAX N N') x) +
      mdist m (f (MAX N N') x, g x)` THEN
   HYP SIMP_TAC "fwd x gwd" [MDIST_TRIANGLE] THEN
   TRANS_TAC REAL_LTE_TRANS `e / &2 + e / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD2; REWRITE_TAC[REAL_HALF; REAL_LE_REFL]] THEN
   CONJ_TAC THENL [ALL_TAC; REMOVE_THEN "N'" MATCH_MP_TAC THEN ARITH_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {mdist m (f n x:B,f (MAX N N') x) | x:A IN s}` THEN
   HYP SIMP_TAC "N n" [ARITH_RULE `N <= MAX N N'`] THEN
   HYP SIMP_TAC "sup x" [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [HYP_TAC "cy': @N. N" (C MATCH_MP REAL_LT_01) THEN
   USE_THEN "fbd" (MP_TAC o REWRITE_RULE[MBOUNDED] o SPEC `N:num`) THEN
   HYP REWRITE_TAC "nempty" [mbounded; IMAGE_EQ_EMPTY] THEN
   INTRO_TAC "Nwd (@c b. c Nbd)" THEN
   MAP_EVERY EXISTS_TAC [`c:B`; `b + &1`] THEN
   REWRITE_TAC[SUBSET; IN_IMAGE; IN_MCBALL] THEN
   INTRO_TAC "![y]; (@x. y x)" THEN REMOVE_THEN "y" SUBST1_TAC THEN
   HYP SIMP_TAC "x gwd c" [] THEN TRANS_TAC REAL_LE_TRANS
     `mdist m (c:B, f (N:num) (x:A)) + mdist m (f N x, g x)` THEN
   HYP SIMP_TAC "c fwd gwd x" [MDIST_TRIANGLE] THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [REMOVE_THEN "Nbd" MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    HYP MESON_TAC "x" [];
    REFUTE_THEN (LABEL_TAC "contra" o REWRITE_RULE[REAL_NOT_LE])] THEN
   CLAIM_TAC "@a. a1 a2"
     `?a. &1 < a /\ a < mdist m (f (N:num) (x:A), g x:B)` THENL
   [EXISTS_TAC `(&1 + mdist m (f (N:num) (x:A), g x:B)) / &2` THEN
    REMOVE_THEN "contra" MP_TAC THEN REAL_ARITH_TAC;
    USE_THEN "x" (HYP_TAC "glim" o C MATCH_MP)] THEN
   REMOVE_THEN "glim" (MP_TAC o REWRITE_RULE[LIMIT_METRIC_SEQUENTIALLY]) THEN
   HYP SIMP_TAC "gwd x" [] THEN DISCH_THEN (MP_TAC o SPEC `a - &1`) THEN
   ANTS_TAC THENL [REMOVE_THEN "a1" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "@N'. N'" THEN
   CUT_TAC `mdist m (f (N:num) (x:A), g x:B) < a` THENL
   [REMOVE_THEN "a2" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `mdist m (f N (x:A),f (MAX N N') x:B) + mdist m (f (MAX N N') x,g x)` THEN
   HYP SIMP_TAC "fwd gwd x" [MDIST_TRIANGLE] THEN
   SUBST1_TAC (REAL_ARITH `a = &1 + (a - &1)`) THEN
   MATCH_MP_TAC REAL_LT_ADD2 THEN CONJ_TAC THENL
   [ALL_TAC; REMOVE_THEN "N'" MATCH_MP_TAC THEN ARITH_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {mdist m (f N x:B,f (MAX N N') x) | x:A IN s}` THEN
   CONJ_TAC THENL
   [HYP SIMP_TAC "sup x" []; REMOVE_THEN "N" MATCH_MP_TAC THEN ARITH_TAC];
   ALL_TAC] THEN
  INTRO_TAC "!e; e" THEN REMOVE_THEN "unif" (MP_TAC o SPEC `e / &2`) THEN
  HYP REWRITE_TAC "e" [REAL_HALF] THEN INTRO_TAC "@N. N" THEN
  EXISTS_TAC `N:num` THEN INTRO_TAC "!n; n" THEN
  TRANS_TAC REAL_LET_TRANS `e / &2` THEN CONJ_TAC THENL
  [ALL_TAC; REMOVE_THEN "e" MP_TAC THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
  [HYP SET_TAC "nempty" []; HYP MESON_TAC "N n" [REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Metric space of continuous bounded functions.                             *)
(* ------------------------------------------------------------------------- *)

let cfunspace = new_definition
  `cfunspace top m =
   submetric (funspace (topspace top) m)
     {f:A->B | topcontinuous top (mtopology m) f}`;;

let CFUNSPACE = (REWRITE_RULE[GSYM FORALL_AND_THM] o prove)
 (`(!top m.
      mspace (cfunspace top m) =
      {f:A->B | (!x. x IN topspace top ==> f x IN mspace m) /\
                f IN EXTENSIONAL (topspace top) /\
                mbounded m (IMAGE f (topspace top)) /\
                topcontinuous top (mtopology m) f}) /\
     (!f g:A->B.
        mdist (cfunspace top m) (f,g) =
        if topspace top = {} then &0 else
        sup {mdist m (f x,g x) | x IN topspace top})`,
  REWRITE_TAC[cfunspace; SUBMETRIC; FUNSPACE] THEN SET_TAC[]);;

let CFUNSPACE_SUBSET_FUNSPACE = prove
 (`!top:A topology m:B metric.
     mspace (cfunspace top m) SUBSET mspace (funspace (topspace top) m)`,
  SIMP_TAC[SUBSET; FUNSPACE; CFUNSPACE; IN_ELIM_THM]);;

let MDIST_CFUNSPACE_EQ_MDIST_FUNSPACE = prove
 (`!top m f g:A->B.
     mdist (cfunspace top m) (f,g) = mdist (funspace (topspace top) m) (f,g)`,
  REWRITE_TAC[FUNSPACE; CFUNSPACE]);;

let CFUNSPACE_MDIST_LE = prove
 (`!top m f g:A->B a.
     ~(topspace top = {}) /\
     f IN mspace (cfunspace top m) /\
     g IN mspace (cfunspace top m)
     ==> (mdist (cfunspace top m) (f,g) <= a <=>
          !x. x IN topspace top ==> mdist m (f x, g x) <= a)`,
  INTRO_TAC "! *; ne f g" THEN
  REWRITE_TAC[MDIST_CFUNSPACE_EQ_MDIST_FUNSPACE] THEN
  MATCH_MP_TAC FUNSPACE_MDIST_LE THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CFUNSPACE_SUBSET_FUNSPACE]);;

let CFUNSPACE_IMP_BOUNDED2 = prove
 (`!top m f g:A->B.
     f IN mspace (cfunspace top m) /\ g IN mspace (cfunspace top m)
     ==> (?b. !x. x IN topspace top ==> mdist m (f x,g x) <= b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNSPACE_IMP_BOUNDED2 THEN
  ASM SET_TAC [CFUNSPACE_SUBSET_FUNSPACE]);;

let CFUNSPACE_MDIST_LT = prove
 (`!top m f g:A->B a x.
     topspace top compact_in top /\
     f IN mspace (cfunspace top m) /\ g IN mspace (cfunspace top m) /\
     mdist (cfunspace top m) (f, g) < a /\
     x IN topspace top
     ==> mdist m (f x, g x) < a`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `topspace (top:A topology) = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN INTRO_TAC "cpt f g lt x" THEN
  REMOVE_THEN "lt" MP_TAC THEN ASM_REWRITE_TAC[CFUNSPACE] THEN
  INTRO_TAC "lt" THEN
  TRANS_TAC REAL_LET_TRANS
    `sup {mdist m (f x:B,g x) | x:A IN topspace top}` THEN
  HYP SIMP_TAC "lt" [] THEN  MATCH_MP_TAC REAL_LE_SUP THEN
  HYP (DESTRUCT_TAC "@b. b" o
    MATCH_MP CFUNSPACE_IMP_BOUNDED2 o CONJ_LIST) "f g" [] THEN
  MAP_EVERY EXISTS_TAC [`b:real`; `mdist m (f (x:A):B,g x)`] THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN HYP MESON_TAC "x b" []);;

let MDIST_CFUNSPACE_LE = prove
 (`!top m B f g.
     &0 <= B /\
     (!x:A. x IN topspace top ==> mdist m (f x:B, g x) <= B)
     ==> mdist (cfunspace top m) (f,g) <= B`,
  INTRO_TAC "!top m B f g; Bpos bound" THEN
  REWRITE_TAC[CFUNSPACE] THEN COND_CASES_TAC THEN
  HYP REWRITE_TAC "Bpos" [] THEN MATCH_MP_TAC REAL_SUP_LE THEN
  CONJ_TAC THENL
  [POP_ASSUM MP_TAC THEN SET_TAC[];
   REWRITE_TAC[IN_ELIM_THM] THEN HYP MESON_TAC "bound" []]);;

let MDIST_CFUNSPACE_IMP_MDIST_LE = prove
 (`!top m f g:A->B a x.
     f IN mspace (cfunspace top m) /\
     g IN mspace (cfunspace top m) /\
     mdist (cfunspace top m) (f,g) <= a /\
     x IN topspace top
     ==> mdist m (f x,g x) <= a`,
  MESON_TAC[MEMBER_NOT_EMPTY; CFUNSPACE_MDIST_LE]);;

let COMPACT_IN_MSPACE_CFUNSPACE = prove
 (`!top m.
     topspace top compact_in top
     ==> mspace (cfunspace top m) =
          {f | (!x:A. x IN topspace top ==> f x:B IN mspace m) /\
               f IN EXTENSIONAL (topspace top) /\
               topcontinuous top (mtopology m) f}`,
  REWRITE_TAC[CFUNSPACE; EXTENSION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN SIMP_TAC[] THEN INTRO_TAC "wd ext cont" THEN
  MATCH_MP_TAC COMPACT_IN_IMP_MBOUNDED THEN
  MATCH_MP_TAC (ISPEC `top:A topology` IMAGE_COMPACT_IN) THEN
  ASM_REWRITE_TAC[]);;

let MCOMPLETE_CFUNSPACE = prove
 (`!top:A topology m:B metric. mcomplete m ==> mcomplete (cfunspace top m)`,
  INTRO_TAC "!top m; cpl" THEN REWRITE_TAC[cfunspace] THEN
  MATCH_MP_TAC SEQUENTIALLY_CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN
  ASM_SIMP_TAC[MCOMPLETE_FUNSPACE] THEN
  REWRITE_TAC[IN_ELIM_THM; LIMIT_METRIC_SEQUENTIALLY] THEN
  INTRO_TAC "![f] [g]; fcont g lim" THEN
  ASM_CASES_TAC `topspace top = {}:A->bool` THENL
  [ASM_REWRITE_TAC[topcontinuous; NOT_IN_EMPTY; EMPTY_GSPEC; OPEN_IN_EMPTY];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  REWRITE_TAC[TOPCONTINUOUS_TO_METRIC; IN_MBALL] THEN
  INTRO_TAC "!x; x; ![e]; e" THEN CLAIM_TAC "e3pos" `&0 < e / &3` THENL
  [REMOVE_THEN "e" MP_TAC THEN REAL_ARITH_TAC;
   USE_THEN "e3pos" (HYP_TAC "lim: @N. N" o C MATCH_MP)] THEN
  HYP_TAC "N: f lt" (C MATCH_MP (SPEC `N:num` LE_REFL)) THEN
  HYP_TAC "fcont" (REWRITE_RULE[TOPCONTINUOUS_TO_METRIC]) THEN
  USE_THEN "x" (HYP_TAC "fcont" o C MATCH_MP) THEN
  USE_THEN "e3pos" (HYP_TAC "fcont" o C MATCH_MP) THEN
  HYP_TAC "fcont: @u. u x' inc" (SPEC `N:num`) THEN EXISTS_TAC `u:A->bool` THEN
  HYP REWRITE_TAC "u x'" [] THEN INTRO_TAC "!y; y'" THEN
  CLAIM_TAC "uinc" `!x:A. x IN u ==> x IN topspace top` THENL
  [REMOVE_THEN "u" (MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
   ALL_TAC] THEN
  HYP_TAC "g -> gwd gext gbd" (REWRITE_RULE[FUNSPACE; IN_ELIM_THM]) THEN
  HYP_TAC "f -> fwd fext fbd" (REWRITE_RULE[FUNSPACE; IN_ELIM_THM]) THEN
  CLAIM_TAC "y" `y:A IN topspace top` THENL
  [HYP SIMP_TAC "uinc y'" [OPEN_IN_SUBSET]; HYP SIMP_TAC "gwd x y" []] THEN
  CLAIM_TAC "sup" `!x0:A. x0 IN topspace top
                          ==> mdist m (f (N:num) x0:B,g x0) <= e / &3` THENL
  [INTRO_TAC "!x0; x0" THEN TRANS_TAC REAL_LE_TRANS
     `sup {mdist m (f (N:num) x,g x:B) | x:A IN topspace top}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_SUP THEN HYP (DESTRUCT_TAC "@b. b" o
      MATCH_MP FUNSPACE_IMP_BOUNDED2 o CONJ_LIST) "f g" [] THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `mdist m (f (N:num) (x0:A), g x0:B)`] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    CONJ_TAC THENL [HYP SET_TAC "x0" []; HYP MESON_TAC "b" []];
    REMOVE_THEN "lt" MP_TAC THEN HYP REWRITE_TAC "nempty" [FUNSPACE] THEN
    MATCH_ACCEPT_TAC REAL_LT_IMP_LE];
   ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
    `mdist m (g (x:A):B, f (N:num) x) + mdist m (f N x, g y)` THEN
  HYP SIMP_TAC "gwd fwd x y" [MDIST_TRIANGLE] THEN
  SUBST1_TAC (ARITH_RULE `e = e / &3 + (e / &3 + e / &3)`) THEN
  MATCH_MP_TAC REAL_LET_ADD2 THEN HYP SIMP_TAC "gwd fwd x sup" [MDIST_SYM] THEN
  TRANS_TAC REAL_LET_TRANS
    `mdist m (f (N:num) (x:A):B, f N y) + mdist m (f N y, g y)` THEN
  HYP SIMP_TAC "fwd gwd x y" [MDIST_TRIANGLE] THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN HYP SIMP_TAC "gwd fwd y sup" [] THEN
  REMOVE_THEN "inc" MP_TAC THEN HYP SIMP_TAC "fwd x y' uinc" [IN_MBALL]);;

(* ------------------------------------------------------------------------- *)
(* The Baire Category theorem for complete metric spaces.                    *)
(* ------------------------------------------------------------------------- *)

let METRIC_BAIRE_CATEGORY = prove
 (`!m:A metric g.
     mcomplete m /\
     COUNTABLE g /\
     (!t. t IN g ==> open_in (mtopology m) t /\
                     mtopology m closure_of t = mspace m)
     ==> mtopology m closure_of INTERS g = mspace m`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN INTRO_TAC "!m; m" THEN
  REWRITE_TAC[FORALL_COUNTABLE_AS_IMAGE; NOT_IN_EMPTY; CLOSURE_OF_UNIV;
  INTERS_0; TOPSPACE_MTOPOLOGY; FORALL_IN_IMAGE; IN_UNIV; FORALL_AND_THM] THEN
  INTRO_TAC "![u]; u_open u_dense" THEN
  REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY] THEN
  IMP_REWRITE_TAC[DENSE_INTERSECTS_OPEN] THEN CONJ_TAC THENL
  [ALL_TAC;
   MATCH_MP_TAC INTERS_SUBSET THEN CONJ_TAC THENL
   [CUT_TAC `u 0:A->bool IN IMAGE u (:num)` THENL
    [SET_TAC[]; REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
    HYP MESON_TAC "u_open" [OPEN_IN_SUBSET]]] THEN
  INTRO_TAC "![w]; w_open w_ne" THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  CLAIM_TAC "@x0. x0" `?x0:A. x0 IN u 0 INTER w` THENL
  [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
   SUBGOAL_THEN `u 0:A->bool SUBSET topspace (mtopology m)`
    (MP_TAC o MATCH_MP DENSE_INTERSECTS_OPEN) THENL
   [HYP SIMP_TAC "u_open" [OPEN_IN_SUBSET]; ALL_TAC] THEN
   HYP REWRITE_TAC "u_dense" [TOPSPACE_MTOPOLOGY] THEN
   ASM_SIMP_TAC[]; ALL_TAC] THEN
  CLAIM_TAC "@r0. r0pos r0lt1 sub"
    `?r. &0 < r /\ r < &1 /\ mcball m (x0:A,r) SUBSET u 0 INTER w` THENL
  [SUBGOAL_THEN `open_in (mtopology m) (u 0 INTER w:A->bool)` MP_TAC THENL
   [HYP SIMP_TAC "u_open w_open" [OPEN_IN_INTER]; ALL_TAC] THEN
   REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN INTRO_TAC "u0w hp" THEN
   REMOVE_THEN "hp" (MP_TAC o SPEC `x0:A`) THEN
   ANTS_TAC THENL [HYP REWRITE_TAC "x0" []; ALL_TAC] THEN
   INTRO_TAC "@r. rpos ball" THEN EXISTS_TAC `min r (&1) / &2` THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC SUBSET_TRANS `mball m (x0:A,r)` THEN
   HYP REWRITE_TAC "ball" [] THEN
   MATCH_MP_TAC MCBALL_SUBSET_MBALL_CONCENTRIC THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (DESTRUCT_TAC "@b. b0 b1" o prove_general_recursive_function_exists)
    `?b:num->(A#real).
       b 0 = (x0:A,r0) /\
       (!n. b (SUC n) =
            @(x,r). &0 < r /\ r < SND (b n) / &2 /\ x IN mspace m /\
                    mcball m (x,r) SUBSET mball m (b n) INTER u n)` THEN
  CLAIM_TAC "rmk"
    `!n. (\ (x:A,r). &0 < r /\ r < SND (b n) / &2 /\ x IN mspace m /\
                   mcball m (x,r) SUBSET mball m (b n) INTER u n)
         (b (SUC n))` THENL
  [LABEL_INDUCT_TAC THENL
   [REMOVE_THEN "b1" (fun b1 -> REWRITE_TAC[b1]) THEN
    MATCH_MP_TAC CHOICE_PAIRED_THM THEN
    REMOVE_THEN "b0" (fun b0 -> REWRITE_TAC[b0]) THEN
    MAP_EVERY EXISTS_TAC [`x0:A`; `r0 / &4`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [CUT_TAC `u 0:A->bool SUBSET mspace m` THENL
     [HYP SET_TAC "x0" [];
      HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
     ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS `mball m (x0:A,r0)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC MCBALL_SUBSET_MBALL_CONCENTRIC THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[SUBSET_INTER; SUBSET_REFL] THEN
     TRANS_TAC SUBSET_TRANS `mcball m (x0:A,r0)` THEN
     REWRITE_TAC [MBALL_SUBSET_MCBALL] THEN HYP SET_TAC "sub" []];
    ALL_TAC] THEN
   USE_THEN "b1" (fun b1 -> GEN_REWRITE_TAC RAND_CONV [b1]) THEN
   MATCH_MP_TAC CHOICE_PAIRED_THM THEN REWRITE_TAC[] THEN
   HYP_TAC "ind_n: rpos rlt x subn" (REWRITE_RULE[LAMBDA_UNPAIR_THM]) THEN
   SUBGOAL_THEN `u (SUC n):A->bool SUBSET topspace (mtopology m)`
    (MP_TAC o MATCH_MP DENSE_INTERSECTS_OPEN) THENL
   [HYP SIMP_TAC "u_open" [OPEN_IN_SUBSET]; ALL_TAC] THEN
   HYP REWRITE_TAC "u_dense" [TOPSPACE_MTOPOLOGY] THEN
   DISCH_THEN (MP_TAC o SPEC `mball m (b (SUC n):A#real)`) THEN
   (DESTRUCT_TAC "@x1 r1. bsuc" o MESON[PAIR])
     `?x1:A r1:real. b (SUC n) = x1,r1` THEN
   HYP REWRITE_TAC "bsuc" [] THEN
   REMOVE_THEN "bsuc"
    (fun th -> RULE_ASSUM_TAC (REWRITE_RULE[th]) THEN LABEL_TAC "bsuc" th) THEN
   ANTS_TAC THENL
   [HYP REWRITE_TAC "x" [OPEN_IN_MBALL; MBALL_EQ_EMPTY; DE_MORGAN_THM] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN INTRO_TAC "@z. hp" THEN
   EXISTS_TAC `z:A` THEN
   SUBGOAL_THEN `open_in (mtopology m) (mball m (x1:A,r1) INTER u (SUC n))`
     (DESTRUCT_TAC "hp1 hp2" o REWRITE_RULE[OPEN_IN_MTOPOLOGY_MCBALL]) THENL
   [HYP SIMP_TAC "u_open" [OPEN_IN_INTER; OPEN_IN_MBALL]; ALL_TAC] THEN
   CLAIM_TAC "z" `z:A IN mspace m` THENL
   [CUT_TAC `u (SUC n):A->bool SUBSET mspace m` THENL
    [HYP SET_TAC "hp" [];
     HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
    HYP REWRITE_TAC "z" []] THEN
   REMOVE_THEN "hp2" (MP_TAC o SPEC `z:A`) THEN
   ANTS_TAC THENL [HYP SET_TAC "hp" []; ALL_TAC] THEN
   INTRO_TAC "@r. rpos ball" THEN EXISTS_TAC `min r (r1 / &4)` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC SUBSET_TRANS `mcball m (z:A,r)` THEN
   HYP SIMP_TAC "ball" [MCBALL_SUBSET_CONCENTRIC; REAL_MIN_MIN];
   ALL_TAC] THEN
  CLAIM_TAC "@x r. b" `?x r. !n:num. b n = x n:A, r n:real` THENL
  [MAP_EVERY EXISTS_TAC
     [`FST o (b:num->A#real)`; `SND o (b:num->A#real)`] THEN
   REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  REMOVE_THEN "b"
    (fun b -> RULE_ASSUM_TAC (REWRITE_RULE[b]) THEN LABEL_TAC "b" b) THEN
  HYP_TAC "b0: x_0 r_0" (REWRITE_RULE[PAIR_EQ]) THEN
  REMOVE_THEN "x_0" (SUBST_ALL_TAC o GSYM) THEN
  REMOVE_THEN "r_0" (SUBST_ALL_TAC o GSYM) THEN
  HYP_TAC "rmk: r1pos r1lt x1 ball" (REWRITE_RULE[FORALL_AND_THM]) THEN
  CLAIM_TAC "x" `!n:num. x n:A IN mspace m` THENL
  [LABEL_INDUCT_TAC THENL
   [CUT_TAC `u 0:A->bool SUBSET mspace m` THENL
    [HYP SET_TAC "x0" [];
     HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
    HYP REWRITE_TAC "x1" []];
   ALL_TAC] THEN
  CLAIM_TAC "rpos" `!n:num. &0 < r n` THENL
  [LABEL_INDUCT_TAC THENL
   [HYP REWRITE_TAC "r0pos" []; HYP REWRITE_TAC "r1pos" []];
   ALL_TAC] THEN
  CLAIM_TAC "rmono" `!p q:num. p <= q ==> r q <= r p` THENL
  [MATCH_MP_TAC LE_INDUCT THEN REWRITE_TAC[REAL_LE_REFL] THEN
   INTRO_TAC "!p q; pq rpq" THEN
   REMOVE_THEN "r1lt" (MP_TAC o SPEC `q:num`) THEN
   REMOVE_THEN "rpos" (MP_TAC o SPEC `q:num`) THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  CLAIM_TAC "rlt" `!n:num. r n < inv (&2 pow n)` THENL
  [LABEL_INDUCT_TAC THENL
   [CONV_TAC (RAND_CONV REAL_RAT_REDUCE_CONV) THEN HYP REWRITE_TAC "r0lt1" [];
    TRANS_TAC REAL_LTE_TRANS `r (n:num) / &2` THEN
    HYP REWRITE_TAC "r1lt" [real_pow] THEN REMOVE_THEN "ind_n" MP_TAC THEN
    REMOVE_THEN "rpos" (MP_TAC o SPEC `n:num`) THEN CONV_TAC REAL_FIELD];
   ALL_TAC] THEN
  CLAIM_TAC "nested"
    `!p q:num. p <= q ==> mball m (x q:A, r q) SUBSET mball m (x p, r p)` THENL
  [MATCH_MP_TAC LE_INDUCT THEN REWRITE_TAC[SUBSET_REFL] THEN
   INTRO_TAC "!p q; pq sub" THEN
   TRANS_TAC SUBSET_TRANS `mball m (x (q:num):A,r q)` THEN
   HYP REWRITE_TAC "sub" [] THEN
   TRANS_TAC SUBSET_TRANS `mcball m (x (SUC q):A,r(SUC q))` THEN
   REWRITE_TAC[MBALL_SUBSET_MCBALL] THEN HYP SET_TAC "ball" [];
   ALL_TAC] THEN
  CLAIM_TAC "in_ball" `!p q:num. p <= q ==> x q:A IN mball m (x p, r p)` THENL
  [INTRO_TAC "!p q; le" THEN CUT_TAC `x (q:num):A IN mball m (x q, r q)` THENL
   [HYP SET_TAC "nested le" []; HYP SIMP_TAC "x rpos" [CENTRE_IN_MBALL_EQ]];
   ALL_TAC] THEN
  CLAIM_TAC "@l. l" `?l:A. limit (mtopology m) x l sequentially` THENL
  [HYP_TAC "m" (REWRITE_RULE[mcomplete]) THEN REMOVE_THEN "m" MATCH_MP_TAC THEN
   HYP REWRITE_TAC "x" [cauchy_in] THEN INTRO_TAC "!e; epos" THEN
   CLAIM_TAC "@N. N" `?N. inv(&2 pow N) < e` THENL
   [REWRITE_TAC[REAL_INV_POW] THEN MATCH_MP_TAC REAL_ARCH_POW_INV THEN
    HYP REWRITE_TAC "epos" [] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   EXISTS_TAC `N:num` THEN MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [HYP SIMP_TAC "x" [MDIST_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
   INTRO_TAC "!n n'; le; n n'" THEN
   TRANS_TAC REAL_LT_TRANS `inv (&2 pow N)` THEN HYP REWRITE_TAC "N" [] THEN
   TRANS_TAC REAL_LT_TRANS `r (N:num):real` THEN HYP REWRITE_TAC "rlt" [] THEN
   CUT_TAC `x (n':num):A IN mball m (x n, r n)` THENL
   [HYP REWRITE_TAC "x" [IN_MBALL] THEN INTRO_TAC "hp" THEN
    TRANS_TAC REAL_LTE_TRANS `r (n:num):real` THEN
    HYP SIMP_TAC "n rmono hp" [];
    HYP SIMP_TAC "in_ball le" []];
   ALL_TAC] THEN
  EXISTS_TAC `l:A` THEN
  CLAIM_TAC "in_mcball" `!n:num. l:A IN mcball m (x n, r n)` THENL
  [GEN_TAC THEN
   (MATCH_MP_TAC o ISPECL [`sequentially`; `mtopology (m:A metric)`])
   LIMIT_IN_CLOSED_IN THEN EXISTS_TAC `x:num->A` THEN
   HYP REWRITE_TAC "l" [TRIVIAL_LIMIT_SEQUENTIALLY; CLOSED_IN_MCBALL] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `n:num` THEN
   INTRO_TAC "![p]; p" THEN CUT_TAC `x (p:num):A IN mball m (x n, r n)` THENL
   [SET_TAC[MBALL_SUBSET_MCBALL]; HYP SIMP_TAC "in_ball p" []];
   ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
   LABEL_INDUCT_TAC THENL
   [HYP SET_TAC "in_mcball sub " []; HYP SET_TAC "in_mcball ball " []];
   HYP SET_TAC "sub in_mcball" []]);;
