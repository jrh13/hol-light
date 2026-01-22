(* ========================================================================= *)
(* Generic-length analog of bit-blasting using automata.                     *)
(* ========================================================================= *)

needs "Library/rstc.ml";;
needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Use reachable states (or any overapproximation) to verify reachability.   *)
(* ------------------------------------------------------------------------- *)

let OVERAPPROXIMATE_REACHABLE = prove
 (`!init step final invariant.
        (!s. init s ==> invariant s) /\
        (!s s'. invariant s /\ step s s' ==> invariant s') /\
        (!s. invariant s ==> final s)
        ==> (!s s':S. init s /\ RTC step s s' ==> final s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s s':S. init s /\ RTC step s s' ==> invariant s'` MP_TAC THENL
   [REWRITE_TAC[IMP_CONJ_ALT; RIGHT_FORALL_IMP_THM]; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC RTC_INDUCT_L THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Classic "model checking" forward reachability fixpoint loop with BDDs.    *)
(*                                                                           *)
(* The states P_k reachable in <= k steps from the initial state P are       *)
(*                                                                           *)
(*       P_0 s <=> P s                                                       *)
(*   P_{k+1} s <=> P_k s \/ ?s'. P_k s' /\ R s' s                            *)
(*                                                                           *)
(* To avoid additional renaming, which is fiddlier with inference-based      *)
(* BDDs, we derive pairs (P_k s,P_k s') in the main recursion step.          *)
(* ------------------------------------------------------------------------- *)

let REACHABLE_STATE_TAC ((asl,w) as gl) =
  let istm,ftm = dest_imp(snd(strip_forall w)) in
  let itm,stm = dest_conj istm in
  let pinit = rator itm
  and ptrans = lhand(rator stm)
  and pfinal' = rator ftm in
  let k = length(striplist dest_pair(fst(dest_gabs(rator itm)))) in
  let _ = remark("State space size 2^" ^ string_of_int k ^
                 " = " ^ string_of_num(pow2 k)) in
  let [tup;tup'],trans = strip_gabs ptrans in
  let tup'',init = dest_gabs pinit in
  let _ = if tup <> tup'' then failwith "inconsistent variables" else () in
  let tup''',final' = dest_gabs pfinal' in
  let _ = if tup' <> tup''' then failwith "inconsistent variables" else () in
  let vars = striplist dest_pair tup and vars' = striplist dest_pair tup' in
  let vt = mk_vtable (length vars + length vars')
  and ut = mk_utable() and ct = mk_ctable() in
  let bddstate = (vt,ut,ct) in
  let bddvars = itlist (fun (a,b) c -> a::b::c) (zip vars vars') [] in
  let _ = do_list (ignore o BDD_VAR bddstate) bddvars in
  let bdd_trans = BDD_OF_TERM undefined bddstate trans
  and bdd_init = BDD_OF_TERM undefined bddstate init in
  let twizzle = vsubst (zip vars vars' @ zip vars' vars) in
  let trans' = twizzle trans
  and init' = twizzle init
  and final = twizzle final' in
  let bdd_trans' = BDD_OF_TERM undefined bddstate trans'
  and bdd_init' = BDD_OF_TERM undefined bddstate init' in
  let step (pk,pk') =
    (BDD_OR bddstate
            (pk,itlist (BDD_EXISTS bddstate) vars'
                       (BDD_AND bddstate (pk',bdd_trans'))),
     BDD_OR bddstate
            (pk',itlist (BDD_EXISTS bddstate) vars
                       (BDD_AND bddstate (pk,bdd_trans)))) in
  let reachedfix before after =
    let ok = fst(fst before) = fst(fst after)
    and ok' = fst(snd before) = fst(snd after) in
    if ok <> ok' then failwith "reachedfix: sanify check"
    else ok in
  let fixpoint =
    let rec aux n p =
      let p' = step p in
      if reachedfix p p' then
        (report
          ("Fixpoint reached after "^string_of_int n^" iteration"^
           (if n = 1 then "" else "s"));
         (p,p'))
      else
        (remark ("No fixpoint after iteration "^string_of_int n);
         aux (n + 1) p') in
    aux 1 in
  let p0 = (bdd_init,bdd_init') in
  let (pk,pk'),(pl,pl') = fixpoint p0 in
  let bdd_final = BDD_OF_TERM undefined bddstate final in
  let th_init = EQT_ELIM(snd(BDD_IMP bddstate (bdd_init,pk)))
  and th_fix = TRANS (snd pl) (SYM(snd pk))
  and th_final = EQT_ELIM(snd(BDD_IMP bddstate (pk,bdd_final))) in
  let th_init' = GENL vars th_init
  and th_fix' =
    GENL (vars @ vars')
         (SPECL (vars' @ vars)
     (GENL vars
      (funpow (length vars) (PURE_ONCE_REWRITE_RULE[LEFT_IMP_EXISTS_THM])
           (MATCH_MP(TAUT `(p \/ q <=> r) ==> q ==> r`) th_fix))))
  and th_final = GENL vars th_final in
  let vtm = mk_gabs(tup,lhand(concl(snd pk))) in
  let pva = mk_var("P",rev_itlist mk_fun_ty (map type_of vars) aty) in
  let rth = GEN_BETA_CONV(mk_comb(mk_gabs(tup,list_mk_comb(pva,vars)),tup)) in
  (MATCH_MP_TAC OVERAPPROXIMATE_REACHABLE THEN
   PURE_REWRITE_TAC[FORALL_PAIR_THM] THEN EXISTS_TAC vtm THEN
   PURE_REWRITE_TAC[rth] THEN
   CONJ_TAC THENL [ACCEPT_TAC th_init'; ALL_TAC] THEN
   CONJ_TAC THENL [ACCEPT_TAC th_fix'; ACCEPT_TAC th_final]) gl;;

(* ------------------------------------------------------------------------- *)
(* Expand multi-bit shifts into repeated 1-bit shifts.                       *)
(* ------------------------------------------------------------------------- *)

let EXPAND_SHIFT_CONV =
  let pth = prove
   (`(!x n. word_shl x (SUC n):N word = word_shl (word_shl x 1) n) /\
     (!x n. word_ushr x (SUC n):N word = word_ushr (word_ushr x 1) n) /\
     (!x n. word_ishr x (SUC n):N word = word_ishr (word_ishr x 1) n)`,
    REWRITE_TAC[WORD_SHL_COMPOSE; WORD_USHR_COMPOSE; WORD_ISHR_COMPOSE] THEN
    REWRITE_TAC[ADD1; ADD_SYM]) in
  let baseconv = GEN_REWRITE_CONV I
    [WORD_SHL_ZERO; WORD_USHR_ZERO; WORD_ISHR_ZERO]
  and stepconv = GEN_REWRITE_CONV I [pth] in
  let rec conv tm =
    match tm with
      Comb(Comb(_,_),ntm) ->
        let n = dest_small_numeral ntm in
        if n = 0 then baseconv tm
        else if n = 1 then REFL tm
        else (RAND_CONV num_CONV THENC stepconv THENC conv) tm
    | _ -> failwith "EXPAND_SHIFT_CONV: inapplicable" in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_shl",_),x),ntm)
    | Comb(Comb(Const("word_ushr",_),x),ntm)
    | Comb(Comb(Const("word_ishr",_),x),ntm) ->
        if is_numeral ntm && not(dest_small_numeral ntm = 1) then conv tm
        else failwith "EXPAND_SHIFT_CONV: inapplicable"
    | _ -> failwith "EXPAND_SHIFT_CONV: inapplicable";;

(* ------------------------------------------------------------------------- *)
(* A useful operation for both shifts and specific numerals.                 *)
(* ------------------------------------------------------------------------- *)

let word_shladd = define
 `word_shladd (x:N word) b = word_or (word_shl x 1) (word(bitval b))`;;

let WORD_SHLADD = prove
 (`!(x:N word) b.
        word_shladd (x:N word) b = word_add (word_shl x 1) (word(bitval b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shladd] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_ADD_OR THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WORD_AND_0; WORD_AND_1; BIT_WORD_SHL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BIT_WORD_SHLADD = prove
 (`(!(x:N word) b. bit 0 (word_shladd x b) <=> b) /\
   (!(x:N word) b i. bit (i + 1) (word_shladd x b) <=>
                     i + 1 < dimindex(:N) /\ bit i x)`,
  REWRITE_TAC[word_shladd; BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_BITVAL] THEN
  SIMP_TAC[ADD_EQ_0; LE_1; ADD_SUB; ARITH_EQ; DIMINDEX_NONZERO] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJ_ACI]);;

let WORD_SHLADD_0 = prove
 (`!x:N word. word_shladd x F = word_shl x 1`,
  REWRITE_TAC[word_shladd; BITVAL_CLAUSES; WORD_OR_0]);;

let WORD_NUMERAL_SHLADD = prove
 (`word(NUMERAL(BIT0 n)):N word = word_shladd (word(NUMERAL n)) F /\
   word(NUMERAL(BIT1 n)):N word = word_shladd (word(NUMERAL n)) T`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
  REWRITE_TAC[WORD_SHLADD; BITVAL_CLAUSES; WORD_OR_0; ADD1] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Expressing right shifts in terms of left, and characterizing top bit.     *)
(* ------------------------------------------------------------------------- *)

let WORD_USHR_SHLADD,WORD_ISHR_SHLADD = (CONJ_PAIR o prove)
 (`(!x y:N word.
        word_ushr x 1 = y <=>
        word_and word_INT_MIN y = word 0 /\
        word_shladd y (bit 0 x) = x) /\
   (!x y:N word.
        word_ishr x 1 = y <=>
        word_and word_INT_MIN y = word_and word_INT_MIN x /\
        word_shladd y (bit 0 x) = x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_INT_MIN] THEN
  REWRITE_TAC[word_shladd; BIT_WORD_OR; BIT_WORD_BITVAL] THEN
  SIMP_TAC[BIT_WORD_SHL; BIT_WORD_USHR; BIT_WORD_ISHR; BIT_WORD_0] THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [BIT_GUARD]; ALL_TAC] THEN
  SIMP_TAC[ARITH_RULE `i < n ==> (i + 1 < n <=> ~(i = n - 1))`] THEN
  CONV_TAC(LAND_CONV(SIMP_CONV[DIMINDEX_NONZERO; ARITH_RULE
            `~(n = 0) ==> (i < n <=> i = n - 1 \/ i < n - 1)`])) THEN
  SIMP_TAC[LT_IMP_NE; TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  (BINOP_TAC THENL
    [MESON_TAC[DIMINDEX_NONZERO; ARITH_RULE `n - 1 < n <=> ~(n = 0)`];
     ALL_TAC]) THEN
  GEN_REWRITE_TAC RAND_CONV [MESON[num_CASES]
   `(!i. P i) <=> P 0 /\ (!i. P(SUC i))`] THEN
  SIMP_TAC[NOT_SUC; LE_1; ARITH_LE; ARITH_LT; SUC_SUB1; GSYM ADD1] THEN
  MESON_TAC[ARITH_RULE `i < n - 1 <=> SUC i < n`]);;

let DEFINE_WORD_INT_MIN = prove
 (`~(word_INT_MIN:N word = word 0) /\
   word_shladd word_INT_MIN F :N word = word 0`,
  REWRITE_TAC[WORD_SHLADD_0; word_INT_MIN; WORD_RULE
   `word_shl (iword x) 1 = iword(&2 * x)`] THEN
  REWRITE_TAC[WORD_IWORD; IWORD_EQ; INT_MUL_RNEG] THEN
  REWRITE_TAC[INTEGER_RULE `(--x:int == &0) (mod n) <=> n divides x`] THEN
  SIMP_TAC[GSYM(CONJUNCT2 INT_POW); DIMINDEX_NONZERO;
           ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_divides] THEN
  REWRITE_TAC[NUMBER_RULE `(n:num) divides n`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  REWRITE_TAC[LE_EXP; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[DIMINDEX_NONZERO; ARITH_RULE `n <= n - 1 <=> n = 0`]);;

(* ------------------------------------------------------------------------- *)
(* Expressing inequalities in terms of the top bit.                          *)
(* ------------------------------------------------------------------------- *)

let VAL_LT_ELIM_THM = prove
 (`!x y:N word.
        val x < val y <=>
        ~(word_and word_INT_MIN
                   (word_or (word_and (word_not x) y)
                            (word_and (word_or (word_not x) y)
                                      (word_sub x y))) =
          word 0)`,
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_INT_MIN; BIT_WORD_0] THEN
  SIMP_TAC[FORALL_UNWIND_THM2; TAUT `~(p /\ q /\ r) <=> q ==> p ==> ~r`] THEN
  CONV_TAC WORD_ARITH);;

let IVAL_LT_ELIM_THM = prove
 (`!x y:N word.
        ival x < ival y <=>
        ~(word_and word_INT_MIN
                   (word_or (word_and x (word_not y))
                            (word_and (word_not(word_xor x y))
                                      (word_sub x y))) =
          word 0)`,
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_INT_MIN; BIT_WORD_0] THEN
  SIMP_TAC[FORALL_UNWIND_THM2; TAUT `~(p /\ q /\ r) <=> q ==> p ==> ~r`] THEN
  CONV_TAC WORD_ARITH);;

let IVAL_LT_0_ELIM_THM = prove
 (`!x:N word.
        ival x < &0 <=> ~(word_and word_INT_MIN x = word 0)`,
  REWRITE_TAC[GSYM MSB_IVAL; WORD_EQ_BITS; BIT_WORD_AND;
              BIT_WORD_INT_MIN; BIT_WORD_0] THEN
  SIMP_TAC[FORALL_UNWIND_THM2; TAUT `~(p /\ q /\ r) <=> q ==> p ==> ~r`] THEN
  CONV_TAC WORD_ARITH);;

(* ------------------------------------------------------------------------- *)
(* Useful to reduce to the Horn case.                                        *)
(* ------------------------------------------------------------------------- *)

let CONJ_WORD_EQ_0 = GSYM WORD_OR_EQ_0;;

let DISJ_WORD_EQ_0 = prove
 (`!x y:N word.
        x = word 0 \/ y = word 0 <=>
        word_and (word_or x (word_neg x)) (word_or y (word_neg y)) = word 0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_AND; BIT_WORD_OR_NEG; BIT_WORD_0] THEN
  MESON_TAC[LE_CASES; LET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Identify shift-right terms, and terms involving carry from bit i to i + 1 *)
(* ------------------------------------------------------------------------- *)

let is_shr tm =
  match tm with
    Comb(Comb(Const("word_ushr",_),_),_) -> true
  | Comb(Comb(Const("word_ishr",_),_),_) -> true
  | _ -> false;;

let carrying tm =
  match tm with
    Comb(Comb(Const("word_add",_),_),_) -> true
  | Comb(Comb(Const("word_sub",_),_),_) -> true
  | Comb(Comb(Const("word_shladd",_),_),_) -> true
  | Comb(Const("word_neg",_),
         Comb(Const("word",_),
              Comb(Const("bitval",_),_))) -> false
  | Comb(Const("word_neg",_),_) -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Convert canonical goal into Boolean reachability.                         *)
(* ------------------------------------------------------------------------- *)

let WORD_AUTO_TRANSIFY_TAC =
  let pth = prove
   (`!step init final b n.
          (!s s':S. init s /\ RTC step s s' ==> final s')
          ==> init(b 0)
              ==> (!i. i + 1 < n ==> step (b i) (b(i+1)))
                  ==> !i. i < n ==> final(b i)`,
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `!i. i < n ==> RTC step ((b:num->S) 0) (b i)`
    MP_TAC THENL [MATCH_MP_TAC num_INDUCTION; ASM_MESON_TAC[]] THEN
    ASM_MESON_TAC[RTC_RULES; ADD1; ARITH_RULE `i + 1 < n ==> i < n`]) in
  let n_ty = `:N` and plus = `(+):num->num->num` and one_tm = `1` in
  let has_word_ty tm =
    match type_of tm with
      Tyapp("word",[_]) -> true
    | _ -> false
  and boolify tm =
    match tm with
      Var(s,t) -> mk_var(s,bool_ty)
    | _ -> failwith "boolify"
  and mk_bit itm tm =
    match type_of tm with
      Tyapp("word",[nty]) -> mk_comb(mk_comb(mk_const("bit",[nty,n_ty]),itm),tm)
    | _ -> failwith "mk_bit"
  and plus1 itm = mk_comb(mk_comb(plus,itm),one_tm) in
  fun (asl,w as gl) ->
    let wvs = filter has_word_ty (frees w) in
    let bvs = variants (frees w) (map boolify wvs) in
    let bvs' = variants (bvs @ frees w) bvs in
    let btup = end_itlist (curry mk_pair) bvs
    and btup' = end_itlist (curry mk_pair) bvs' in
    let init,stepconc = dest_imp w in
    let init' =
      mk_gabs(btup,subst (zip bvs (map (mk_bit `0`) wvs)) init) in
    let step,conc = dest_imp stepconc in
    let itm,stepimp = dest_forall step in
    let step' = list_mk_gabs([btup;btup'],
                             subst (zip bvs (map (mk_bit itm) wvs) @
                                    zip bvs' (map (mk_bit (plus1 itm)) wvs))
                                   (rand stepimp)) in
    let jtm,finalimp = dest_forall conc in
    let final' = mk_gabs(btup',
                    subst (zip bvs' (map (mk_bit jtm) wvs)) (rand finalimp)) in
    let th1 = ISPECL [step';init';final'] pth in
    let th2 = REWRITE_RULE[FORALL_PAIR_FUN_THM] th1 in
    let th3 = SPECL (map (curry mk_abs itm o mk_bit itm) wvs) th2 in
    let th4 = CONV_RULE(TOP_DEPTH_CONV GEN_BETA_CONV) th3 in
    MATCH_MP_TAC th4 gl;;

(* ------------------------------------------------------------------------- *)
(* Basic tactic for special Horn s = 0 ==> t = 0 case.                       *)
(* ------------------------------------------------------------------------- *)

let LSB_CARRYING = prove
 (`(!x z:N word. word_neg x = z ==> (bit 0 z <=> bit 0 x)) /\
   (!x y z:N word. word_add x y = z ==> (bit 0 z <=> ~(bit 0 x <=> bit 0 y))) /\
   (!x y z:N word. word_sub x y = z ==> (bit 0 z <=> ~(bit 0 x <=> bit 0 y))) /\
   (!x (z:N word) b. word_shladd x b = z ==> (bit 0 z <=> b)) /\
   (!a b:N word. a = b ==> (bit 0 a <=> bit 0 b))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[BIT_WORD_NEG; BIT_WORD_ADD;
                   BIT_WORD_SUB; BIT_WORD_SHLADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[LE_1; DIMINDEX_NONZERO]);;

let XSB_CARRYING = prove
 (`(!x z:N word.
        word_neg x = z
        ==> !i. i + 1 < dimindex(:N)
                ==> (bit (i + 1) z <=>
                     (bit (i + 1) x <=> ~bit i x /\ ~bit i z))) /\
   (!x y z:N word.
        word_add x y = z
        ==> !i. i + 1 < dimindex(:N)
                ==> (bit (i + 1) z <=>
                     ((bit (i + 1) x <=> bit (i + 1) y) <=>
                      bit i x /\ bit i y \/
                      (bit i x \/ bit i y) /\ ~bit i z))) /\
   (!x y z:N word.
        word_sub x y = z
        ==> !i. i + 1 < dimindex(:N)
                ==> (bit (i + 1) z <=>
                     ((bit (i + 1) x <=> bit (i + 1) y) <=>
                      ~bit i x /\ bit i y \/
                      (~bit i x \/ bit i y) /\ bit i z))) /\
   (!x (z:N word) b.
        word_shladd x b = z
        ==> !i. i + 1 < dimindex(:N) ==> (bit (i + 1) z <=> bit i x)) /\
   (!a b:N word.
        a = b
        ==> !i. i + 1 < dimindex(:N) ==> (bit (i + 1) a = bit (i + 1) b))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN SUBST1_TAC(SYM th)) THEN
  REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [BIT_WORD_NEG; BIT_WORD_ADD; BIT_WORD_SUB; BIT_WORD_SHLADD] THEN
  ASM_REWRITE_TAC[ADD_SUB; ARITH_RULE `~(i + 1 = 0) /\ 1 <= i + 1`]);;

let ABBREVIATE_SHR_TAC ((asl,w) as gl) =
   match sort free_in (find_terms is_shr w) with
     t::_ -> ABBREV_TAC(mk_eq(genvar(type_of t),t)) gl
   | _ -> failwith "ABBREVIATE_SHR_TAC: No word_ushr/word_ishr subterms";;

let ABBREVIATE_CARRYING_TAC ((asl,w) as gl) =
   match sort free_in (find_terms carrying w) with
     t::_ -> ABBREV_TAC(mk_eq(genvar(type_of t),t)) gl
   | _ -> failwith "ABBREVIATE_CARRYING_TAC: No carrying constructs";;

let LSB_CARRY_RULE =
  let rules = map MATCH_MP (CONJUNCTS LSB_CARRYING) in
  fun x -> tryfind (fun f -> f x) rules;;

let XSB_CARRY_RULE =
  let rules = map MATCH_MP (CONJUNCTS XSB_CARRYING) in
  fun x -> tryfind (fun f -> f x) rules;;

let BIT_PUSH_CONV =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_XOR; BIT_WORD_NOT; BIT_WORD_0];;

let LSB_SIMP_CONV =
  BIT_PUSH_CONV THENC
  REWRITE_CONV[MESON[LE_1; DIMINDEX_NONZERO] `0 < dimindex(:N)`];;

let MSB_SIMP_CONV =
  BIT_PUSH_CONV THENC
  REWRITE_CONV[AND_FORALL_THM; TAUT
    `(i + 1 < n ==> p) /\ (i + 1 < n ==> q) <=> (i + 1 < n ==> p /\ q)`] THENC
  SIMP_CONV[ARITH_RULE `i + 1 < dimindex(:N) ==> i < dimindex(:N)`];;

let HORN_WORD_AUTO_TAC =
  REPEAT ABBREVIATE_CARRYING_TAC THEN
  DISCH_THEN(fun th -> if is_eq(concl th) then ASSUME_TAC th else ALL_TAC) THEN
  TRY(GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
      CONV_TAC BIT_PUSH_CONV THEN SIMP_TAC[]) THEN
  ASSUM_LIST (MP_TAC o CONV_RULE MSB_SIMP_CONV o
              end_itlist CONJ o map XSB_CARRY_RULE) THEN
  POP_ASSUM_LIST (MP_TAC o CONV_RULE LSB_SIMP_CONV o
                  end_itlist CONJ o map LSB_CARRY_RULE) THEN
  WORD_AUTO_TRANSIFY_TAC THEN REACHABLE_STATE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Turn clause into the special s = 0 ==> t = 0 Horn clause and call the     *)
(* basic Horn prover (use T ==> t = 0 or s = 0 ==> F if no neg/pos lits).    *)
(* ------------------------------------------------------------------------- *)

let CORE_WORD_AUTO_TAC =
  let true_tm = `T` and false_tm = `F`
  and DEIMP_CONV =
    (GEN_REWRITE_CONV I [TAUT `T ==> p <=> p`; TAUT `p ==> F <=> ~p`] ORELSEC
     GEN_REWRITE_CONV I [TAUT `p ==> q <=> ~p \/ q`]) THENC
    GEN_REWRITE_CONV TOP_SWEEP_CONV [DE_MORGAN_THM]
  and MERGE_CONV =
    GEN_REWRITE_CONV DEPTH_CONV [CONJ_WORD_EQ_0; DISJ_WORD_EQ_0] in
  fun ((asl,w) as gl) ->
    let ndj,pdj = partition is_neg (disjuncts w) in
    let t = mk_imp((if ndj = [] then true_tm else list_mk_conj (map rand ndj)),
                   (if pdj = [] then false_tm else list_mk_disj pdj)) in
    let th1 = TRANS (SYM(DEIMP_CONV t)) (MERGE_CONV t) in
    let th2 = TRANS (DISJ_ACI_RULE(mk_eq(w,lhand(concl th1)))) th1 in
    (CONV_TAC(K th2) THEN HORN_WORD_AUTO_TAC) gl;;

(* ------------------------------------------------------------------------- *)
(* Overall: prenormalize and split up then call the basic tactic.            *)
(* ------------------------------------------------------------------------- *)

let WORD_MUL_SHLADD = prove
 (`!x y:N word.
    word_mul (word_shladd x T) y = word_add (word_shladd (word_mul x y) F) y /\
    word_mul y (word_shladd x T) = word_add (word_shladd (word_mul y x) F) y /\
    word_mul (word_shladd x F) y = word_shladd (word_mul x y) F /\
    word_mul y (word_shladd x F) = word_shladd (word_mul y x) F`,
  REWRITE_TAC[WORD_SHLADD; BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE);;

let CHARACTERIZE_INT_MIN_TAC =
  let is_intmin tm = match tm with
    Const("word_INT_MIN",_) -> true
  | _ -> false
  and n_ty = `:N` in
  fun (asl,w) ->
    let tms = find_terms is_intmin w in
    MAP_EVERY (fun tm ->
      let ty = hd(snd(dest_type(type_of tm))) in
      MP_TAC(INST_TYPE[ty,n_ty] DEFINE_WORD_INT_MIN) THEN
      SPEC_TAC(tm,genvar(type_of tm)) THEN GEN_TAC) tms (asl,w);;

let PURE_WORD_AUTO_TAC =
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN
  REWRITE_TAC[word_ile; word_ilt; word_ige; word_igt; irelational2;
              word_ule; word_ult; word_ige; word_ugt; relational2;
              INT_GT; INT_GE; GSYM INT_NOT_LT; GT; GE; GSYM NOT_LT;
              VAL_LT_ELIM_THM; IVAL_LT_ELIM_THM; IVAL_LT_0_ELIM_THM] THEN
  GEN_REWRITE_TAC TOP_DEPTH_CONV [WORD_NUMERAL_SHLADD] THEN
  GEN_REWRITE_TAC TOP_DEPTH_CONV [WORD_MUL_SHLADD; WORD_MUL_0] THEN
  CONV_TAC NNFC_CONV THEN CONV_TAC PRENEX_CONV THEN REPEAT GEN_TAC THEN
  CONV_TAC(DEPTH_CONV EXPAND_SHIFT_CONV) THEN
  REPEAT ABBREVIATE_SHR_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [WORD_USHR_SHLADD; WORD_ISHR_SHLADD])) THEN
  CHARACTERIZE_INT_MIN_TAC THEN
  CONV_TAC NNFC_CONV THEN
  CONV_TAC CNF_CONV THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC DEPTH_CONV [GSYM WORD_SHLADD_0] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM WORD_XOR_EQ_0] THEN
  GEN_REWRITE_TAC DEPTH_CONV [WORD_XOR_0; WORD_AND_0; WORD_OR_0] THEN
  CORE_WORD_AUTO_TAC;;

let PURE_WORD_AUTO_RULE tm = prove(tm,PURE_WORD_AUTO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Version with an initial sanity check on specific size 4 when there        *)
(* is a single type variable, and defaulting to trying bit-blasting first    *)
(* for the case of no type variables.                                        *)
(* ------------------------------------------------------------------------- *)

let (WORD_AUTO_TAC:tactic) =
  let nty = `:4` in
  fun (asl,w as gl) ->
    match type_vars_in_term w with
      [] -> (BITBLAST_TAC ORELSE PURE_WORD_AUTO_TAC) gl
    | [n] -> let w' = inst[nty,n] w in
             if try concl(BITBLAST_RULE w') = w' with Failure _ -> false
             then (remark "Sanity check for size 4 OK"; PURE_WORD_AUTO_TAC gl)
             else failwith "WORD_AUTO_TAC: Sanity check for size 4 failed!"
    | _ -> failwith "WORD_AUTO_TAC: Multiple generic types not supported";;

let WORD_AUTO_RULE tm = prove(tm,WORD_AUTO_TAC);;
