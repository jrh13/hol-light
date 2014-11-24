(* ========================================================================= *)
(* Interface to prover9.                                                     *)
(* ========================================================================= *)

(**** NB: this is the "prover9" command invoked by HOL Light.
 **** If this doesn't work, set an explicit path to the prover9 binary
 ****)

let prover9 = "prover9";;

(* ------------------------------------------------------------------------- *)
(* Debugging mode (true = keep the Prover9 input and output files)           *)
(* ------------------------------------------------------------------------- *)

let prover9_debugging = ref false;;

(* ------------------------------------------------------------------------- *)
(* Prover9 options. Set to "" for the Prover9 default.                       *)
(* ------------------------------------------------------------------------- *)

let prover9_options = ref
("clear(auto_inference).\n"^
 "clear(auto_denials).\n"^
 "clear(auto_limits).\n"^
 "set(neg_binary_resolution).\n"^
 "set(binary_resolution).\n"^
 "set(paramodulation).\n");;

(* ------------------------------------------------------------------------- *)
(* Find the variables, functions, and predicates excluding equality.         *)
(* ------------------------------------------------------------------------- *)

let rec functions fvs tm (vacc,facc,racc as acc) =
  if is_var tm then
    if mem tm fvs then (vacc,insert tm facc,racc)
    else (insert tm vacc,facc,racc)
  else if is_abs tm then acc else
  let f,args = strip_comb tm in
  itlist (functions fvs) args (vacc,insert f facc,racc);;

let rec signature fvs tm (vacc,facc,racc as acc) =
  if is_neg tm then signature fvs (rand tm) acc
  else if is_conj tm or is_disj tm or is_imp tm or is_iff tm then
    signature fvs (lhand tm) (signature fvs (rand tm) acc)
  else if is_forall tm or is_exists tm or is_uexists tm then
    signature fvs (body(rand tm)) acc
  else if is_eq tm then
    functions fvs (lhand tm) (functions fvs (rand tm) acc)
  else if is_abs tm then acc else
  let r,args = strip_comb tm in
  itlist (functions fvs) args (vacc,facc,insert r racc);;

(* ------------------------------------------------------------------------- *)
(* Shadow first-order syntax. Literal sign is true = positive.               *)
(* ------------------------------------------------------------------------- *)

type folterm = Variable of string | Function of string * folterm list;;

type literal = Literal of bool * string * folterm list;;

(* ------------------------------------------------------------------------- *)
(* Translate clause into shadow syntax.                                      *)
(* ------------------------------------------------------------------------- *)

let rec translate_term (trans_var,trans_fun,trans_rel as trp) tm =
  let f,args = strip_comb tm in
  if defined trans_fun f then
    Function(apply trans_fun f,map (translate_term trp) args)
  else if is_var tm then Variable(apply trans_var tm)
  else failwith("unknown function"^
                (try fst(dest_const tm) with Failure _ -> "??"));;

let translate_atom (trans_var,trans_fun,trans_rel as trp) tm =
  if is_eq tm then
    Literal(true,"=",[translate_term trp (lhand tm);
                      translate_term trp (rand tm)])
  else
    let r,args = strip_comb tm in
    Literal(true,apply trans_rel r,map (translate_term trp) args);;

let rec translate_clause trp tm =
  if is_disj tm then
    translate_clause trp (lhand tm) @ translate_clause trp (rand tm)
  else if is_neg tm then
    let Literal(s,r,args) = translate_atom trp (rand tm) in
    [Literal(not s,r,args)]
  else [translate_atom trp tm];;

(* ------------------------------------------------------------------------- *)
(* Create Prover9 input file for a set of clauses.                           *)
(* ------------------------------------------------------------------------- *)

let rec prover9_of_term tm =
  match tm with
    Variable(s) -> s
  | Function(f,[]) -> f
  | Function(f,args) ->
        f^"("^
        end_itlist (fun s t -> s^","^t) (map prover9_of_term args) ^
        ")";;

let prover9_of_literal lit =
  match lit with
    Literal(s,r,[]) -> if s then r else "-"^r
  | Literal(s,"=",[l;r]) ->
        (if s then "(" else "-(")^
        (prover9_of_term l) ^ " = " ^ (prover9_of_term r)^")"
  | Literal(s,r,args) ->
        (if s then "" else "-")^r^"("^
        end_itlist (fun s t -> s^","^t) (map prover9_of_term args) ^
        ")";;

let rec prover9_of_clause cls =
  match cls with
    [] -> failwith "prover9_of_clause: empty clause"
  | [l] -> prover9_of_literal l
  | l::ls -> prover9_of_literal l ^ " | " ^ prover9_of_clause ls;;

(* ------------------------------------------------------------------------- *)
(* Parse S-expressions.                                                      *)
(* ------------------------------------------------------------------------- *)

type sexp = Atom of string | List of sexp list;;

let atom inp =
  match inp with
    Resword "("::rst -> raise Noparse
  | Resword ")"::rst -> raise Noparse
  | Resword s::rst -> Atom s,rst
  | Ident s::rst -> Atom s,rst
  | [] -> raise Noparse;;

let rec sexpression inp =
  ( atom
 || (a (Resword "(") ++ many sexpression ++ a (Resword ")") >>
     (fun ((_,l),_) -> List l)))
  inp;;

(* ------------------------------------------------------------------------- *)
(* Skip to beginning of proof object.                                        *)
(* ------------------------------------------------------------------------- *)

let rec skipheader i s =
  if String.sub s i 28 = ";; BEGINNING OF PROOF OBJECT"
  then String.sub s (i + 28) (String.length s - i - 28)
  else skipheader (i + 1) s;;

(* ------------------------------------------------------------------------- *)
(* Parse a proof step.                                                       *)
(* ------------------------------------------------------------------------- *)

let parse_proofstep ps =
  match ps with
    List[Atom id; just; formula; Atom "NIL"] -> (id,just,formula)
  | _ -> failwith "unexpected proofstep";;

(* ------------------------------------------------------------------------- *)
(* Convert sexp representation of formula to shadow syntax.                  *)
(* ------------------------------------------------------------------------- *)

let rec folterm_of_sexp sexp =
  match sexp with
    Atom(s) when String.sub s 0 1 = "v" -> Variable s
  | Atom(s) -> Function(s,[])
  | List(Atom f::args) -> Function(f,map folterm_of_sexp args)
  | _ -> failwith "folterm_of_sexp: malformed sexpression term representation";;

let folatom_of_sexp sexp =
  match sexp with
    Atom(r) -> Literal(true,r,[])
  | List(Atom r::args) -> Literal(true,r,map folterm_of_sexp args)
  | _ -> failwith "folatom_of_sexp: malformed sexpression atom representation";;

let folliteral_of_sexp sexp =
  match sexp with
    List[Atom "not";sex] -> let Literal(s,r,args) = folatom_of_sexp sex in
                             Literal(not s,r,args)
  | _ -> folatom_of_sexp sexp;;

let rec folclause_of_sexp sexp =
  match sexp with
    List[Atom "or";sex1;sex2] ->
        folclause_of_sexp sex1 @ folclause_of_sexp sex2
  | _ -> [folliteral_of_sexp sexp];;

(* ------------------------------------------------------------------------- *)
(* Convert shadow syntax back into HOL (sometimes given expected type).      *)
(* Make a crude type postcorrection for equations between variables based    *)
(* on their types in other terms, if applicable.                             *)
(* It might be nicer to use preterms to get a systematic use of context, but *)
(* this is a pretty simple problem.                                          *)
(* ------------------------------------------------------------------------- *)

let rec hol_of_folterm (btrans_fun,btrans_rel as trp) ty tm =
  match tm with
    Variable(x) -> variant (ran btrans_fun) (mk_var(x,ty))
  | Function(fs,args) ->
        let f = apply btrans_fun fs in
        let tys,rty = nsplit dest_fun_ty args (type_of f) in
        list_mk_comb(f,map2 (hol_of_folterm trp) tys args);;

let hol_of_folliteral (btrans_fun,btrans_rel as trp) lit =
  match lit with
    Literal(s,"false",[]) -> if s then mk_const("F",[])
                             else mk_neg(mk_const("F",[]))
  | Literal(s,"=",[l;r]) ->
        let tml_prov = hol_of_folterm trp aty l
        and tmr_prov = hol_of_folterm trp aty r in
        let ty = if type_of tml_prov <> aty then type_of tml_prov
                 else if type_of tmr_prov <> aty then type_of tmr_prov
                 else aty in
        let ptm = mk_eq(hol_of_folterm trp ty l,hol_of_folterm trp ty r) in
        if s then ptm else mk_neg ptm
  | Literal(s,rs,args) ->
        let r = apply btrans_rel rs in
        let tys,rty = nsplit dest_fun_ty args (type_of r) in
        let ptm = list_mk_comb(r,map2 (hol_of_folterm trp) tys args) in
        if s then ptm else mk_neg ptm;;

let is_truevar (bf,_) tm = is_var tm & not(mem tm (ran bf));;

let rec hol_of_folclause trp cls =
  match cls with
    [] -> mk_const("F",[])
  | [c] -> hol_of_folliteral trp c
  | c::cs -> let rawcls = map (hol_of_folliteral trp) cls in
             let is_truevar tm = is_var tm &
                                 not(mem tm (ran(fst trp))) &
                                 not(mem tm (ran(snd trp))) in
             let und,dec = partition
               (fun t -> is_eq t & is_truevar(lhs t) & is_truevar(rhs t))
               rawcls in
             if und = [] or dec = [] then list_mk_disj rawcls else
             let cxt = map dest_var (filter is_truevar (freesl dec)) in
             let correct t =
               try let l,r = dest_eq t in
                   let ls = fst(dest_var l) and rs = fst(dest_var r) in
                   let ty = try assoc ls cxt with Failure _ -> assoc rs cxt in
                   mk_eq(mk_var(ls,ty),mk_var(rs,ty))
               with Failure _ -> t in
             list_mk_disj(map correct rawcls);;

(* ------------------------------------------------------------------------- *)
(* Composed map from sexp to HOL items.                                      *)
(* ------------------------------------------------------------------------- *)

let hol_of_term trp ty sexp = hol_of_folterm trp ty (folterm_of_sexp sexp);;

let hol_of_literal trp sexp = hol_of_folliteral trp (folliteral_of_sexp sexp);;

let hol_of_clause trp sexp = hol_of_folclause trp (folclause_of_sexp sexp);;

(* ------------------------------------------------------------------------- *)
(* Follow paramodulation path                                                *)
(* ------------------------------------------------------------------------- *)

let rec PARA_SUBS_CONV path eth tm =
  match path with
    [] -> if lhs(concl eth) = tm then eth else failwith "PARA_SUBS_CONV"
  | n::rpt -> let f,args = strip_comb tm in
              funpow (length args - n) RATOR_CONV (RAND_CONV
                (PARA_SUBS_CONV rpt eth)) tm;;

(* ------------------------------------------------------------------------- *)
(* Pull forward disjunct in clause using prover9/Ivy director string.        *)
(* ------------------------------------------------------------------------- *)

let FRONT1_DISJ_CONV =
  GEN_REWRITE_CONV I [TAUT `a \/ b \/ c <=> b \/ a \/ c`] ORELSEC
  GEN_REWRITE_CONV I [TAUT `a \/ b <=> b \/ a`];;

let rec FRONT_DISJ_CONV l tm =
  match l with
    [] | ((Atom "1")::_) -> REFL tm
  | (Atom "2")::t -> (RAND_CONV (FRONT_DISJ_CONV t) THENC
                      FRONT1_DISJ_CONV) tm
  | _ -> failwith "unexpected director string in clause";;

(* ------------------------------------------------------------------------- *)
(* For using paramodulating equation, more convenient to put at the back.    *)
(* ------------------------------------------------------------------------- *)

let AP_IMP =
  let pp = MATCH_MP(TAUT `(a ==> b) ==> !x. x \/ a ==> x \/ b`) in
  fun t -> SPEC t o pp;;

let rec PARA_BACK_CONV eqdir tm =
  match eqdir with
    [Atom "1"] when not(is_disj tm) -> REFL tm
  | [Atom "2"] when not(is_disj tm) -> SYM_CONV tm
  | Atom "2"::eqs -> RAND_CONV (PARA_BACK_CONV eqs) tm
  | [Atom "1"; Atom f] when is_disj tm ->
        let th1 = if f = "2" then LAND_CONV SYM_CONV tm else REFL tm in
        let tm' = rand(concl th1) in
        let djs = disjuncts tm' in
        let th2 = DISJ_ACI_RULE(mk_eq(tm',list_mk_disj(tl djs @ [hd djs]))) in
        TRANS th1 th2
  | _ -> failwith "PARA_BACK_CONV";;

(* ------------------------------------------------------------------------- *)
(* Do direct resolution on front clauses.                                    *)
(* ------------------------------------------------------------------------- *)

let RESOLVE =
  let resrules = map (MATCH_MP o TAUT)
   [`a /\ ~a ==> F`;
    `~a /\ a ==> F`;
    `a /\ (~a \/ b) ==> b`;
    `~a /\ (a \/ b) ==> b`;
    `(a \/ b) /\ ~a ==> b`;
    `(~a \/ b) /\ a ==> b`;
    `(a \/ b) /\ (~a \/ c) ==> b \/ c`;
    `(~a \/ b) /\ (a \/ c) ==> b \/ c`] in
  fun th1 th2 -> let th = CONJ th1 th2 in tryfind (fun f -> f th) resrules;;

(* ------------------------------------------------------------------------- *)
(* AC rearrangement of disjunction but maybe correcting proforma types in    *)
(* the target term for equations between variables.                          *)
(* ------------------------------------------------------------------------- *)

let ACI_CORRECT th tm =
  try EQ_MP (DISJ_ACI_RULE(mk_eq(concl th,tm))) th with Failure _ ->
  let cxt = map dest_var (frees(concl th)) in
  let rec correct t =
    if is_disj t then mk_disj(correct(lhand t),correct(rand t))
    else if is_neg t then mk_neg(correct(rand t)) else
    (try let l,r = dest_eq t in
         let ls = fst(dest_var l) and rs = fst(dest_var r) in
         let ty = try assoc ls cxt with Failure _ -> assoc rs cxt in
         mk_eq(mk_var(ls,ty),mk_var(rs,ty))
     with Failure _ -> t) in
  let tm' = correct tm in
  EQ_MP (DISJ_ACI_RULE(mk_eq(concl th,tm'))) th;;

(* ------------------------------------------------------------------------- *)
(* Process proof step.                                                       *)
(* ------------------------------------------------------------------------- *)

let rec PROVER9_PATH_CONV l conv =
  match l with
    Atom "2"::t -> RAND_CONV(PROVER9_PATH_CONV t conv)
  | Atom "1"::t -> LAND_CONV(PROVER9_PATH_CONV t conv)
  | [] -> conv
  | _ -> failwith "PROVER9_PATH_CONV:unknown path";;

let PROVER9_FLIP_CONV tm =
  if is_neg tm then RAND_CONV SYM_CONV tm else SYM_CONV tm;;

let process_proofstep ths trp asms (lab,just,fm) =
  let tm = hol_of_clause trp fm in
  match just with
    List[Atom "input"] ->
        if is_eq tm & lhs tm = rhs tm then REFL(rand tm) else
        tryfind (fun th -> PART_MATCH I th tm) ths
  |  List[Atom "flip"; Atom n; List path] ->
        let th = apply asms n in
        let nth = CONV_RULE(PROVER9_PATH_CONV path PROVER9_FLIP_CONV) th in
        if concl nth = tm then nth
        else failwith "Inconsistency from flip"
  | List[Atom "instantiate"; Atom "0"; List[List[x;Atom".";y]]] ->
        let th = REFL(hol_of_term trp aty y) in
        if concl th = tm then th
        else failwith "Inconsistency from instantiation of reflexivity"
  | List[Atom "instantiate"; Atom n; List i] ->
        let th = apply asms n
        and ilist = map (fun (List[Atom x;Atom"."; y]) -> (y,x)) i in
        let xs = map
         (fun (y,x) -> find_term (fun v -> is_var v & fst(dest_var v) = x)
                                 (concl th)) ilist in
        let ys = map2
          (fun (y,x) v -> hol_of_term trp (type_of v) y) ilist xs in
        INST (zip ys xs) th
  | List[Atom "paramod"; Atom eqid; List eqdir; Atom tmid; List dir] ->
        let eth = CONV_RULE (PARA_BACK_CONV eqdir) (apply asms eqid)
        and tth = apply asms tmid
        and path = (map (fun (Atom s) -> int_of_string s) dir) in
        let etm = concl eth in
        let th =
          if is_disj etm then
            let djs = disjuncts etm in
            let eq = last djs in
            let fth = CONV_RULE (PARA_SUBS_CONV path (ASSUME eq)) tth in
            MP (itlist AP_IMP (butlast djs) (DISCH eq fth)) eth
          else CONV_RULE(PARA_SUBS_CONV path eth) tth in
        if concl th = tm then th
        else failwith "Inconsistency from paramodulation"
  | List[Atom "resolve"; Atom l1; List path1; Atom l2; List path2] ->
        let th1 = CONV_RULE (FRONT_DISJ_CONV path1) (apply asms l1)
        and th2 = CONV_RULE (FRONT_DISJ_CONV path2) (apply asms l2) in
        let th3 = RESOLVE th1 th2 in
        ACI_CORRECT th3 tm
  | List[Atom "propositional"; Atom l] ->
        let th1 = apply asms l in
        ACI_CORRECT th1 tm
  | _ -> failwith "process_proofstep: no translation";;

let rec process_proofsteps ths trp asms steps =
  match steps with
    [] -> asms,[]
  | ((lab,_,_) as st)::sts ->
        (try let th = process_proofstep ths trp asms st in
             process_proofsteps ths trp ((lab |-> th) asms) sts
         with _ -> asms,steps);;

(* ------------------------------------------------------------------------- *)
(* Main refutation procedure for clauses                                     *)
(* ------------------------------------------------------------------------- *)

let PROVER9_REFUTE ths =
  let fvs = itlist (fun th -> union (freesl(hyp th))) ths [] in
  let fovars,functions,relations =
    signature fvs (end_itlist (curry mk_conj) (map concl ths)) ([],[],[]) in
  let trans_var =
    itlist2 (fun f n -> f |-> "x"^string_of_int n)
            fovars (1--length fovars) undefined
  and trans_fun =
    itlist2 (fun f n -> f |-> "f"^string_of_int n)
            functions (1--length functions) undefined
  and trans_rel =
    itlist2 (fun f n -> f |-> "R"^string_of_int n)
            relations (1--length relations) undefined in
  let cls =
    map (translate_clause (trans_var,trans_fun,trans_rel) o concl) ths in
  let p9cls = map (fun c -> prover9_of_clause c ^".\n") cls in
  let p9str = "clear(bell).\n"^ !prover9_options ^
              "formulas(sos).\n"^
              itlist (^) p9cls
              "end_of_list.\n" in
  let filename_in = Filename.temp_file "prover9" ".in"
  and filename_out = Filename.temp_file "prover9" ".out" in
  let _ = file_of_string filename_in p9str in
  let retcode = Sys.command
   (prover9 ^ " -f " ^ filename_in ^ " | prooftrans ivy >" ^ filename_out) in
  if retcode <> 0 then failwith "Prover9 call apparently failed" else
  let p9proof = string_of_file filename_out in
  let _ = if !prover9_debugging then ()
          else (ignore(Sys.remove filename_in);
                ignore(Sys.remove filename_out)) in
  let List sexps,unp = sexpression(lex(explode(skipheader 0 p9proof))) in
  (if unp <> [Ident ";;"; Ident "END"; Ident "OF";
              Ident "PROOF"; Ident "OBJECT"]
   then (Format.print_string "Unexpected proof object tail";
         Format.print_newline())
   else ());
  let btrans_fun = itlist (fun (x,y) -> y |-> x) (graph trans_fun) undefined
  and btrans_rel = itlist (fun (x,y) -> y |-> x) (graph trans_rel) undefined
  and proof = map parse_proofstep sexps in
  let asms,undone =
    process_proofsteps ths (btrans_fun,btrans_rel) undefined proof in
  find (fun th -> concl th = mk_const("F",[])) (map snd (graph asms));;

(* ------------------------------------------------------------------------- *)
(* Hence a prover.                                                           *)
(* ------------------------------------------------------------------------- *)

let PROVER9 =
  let prule = MATCH_MP(TAUT `(~p ==> F) ==> p`)
  and false_tm = `F` and true_tm = `T` in
  let init_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    CONDS_ELIM_CONV THENC
    NNFC_CONV THENC CNF_CONV THENC
    DEPTH_BINOP_CONV `(/\)` (SKOLEM_CONV THENC PRENEX_CONV) THENC
    GEN_REWRITE_CONV REDEPTH_CONV
     [RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM DISJ_ASSOC] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM CONJ_ASSOC] in
  fun tm ->
    let tm' = mk_neg tm in
    let ith = init_conv tm' in
    let itm = rand(concl ith) in
    if itm = true_tm then failwith "PROVER9: formula is trivially false" else
    if itm = false_tm then prule(fst(EQ_IMP_RULE ith)) else
    let evs,bod = strip_exists itm in
    let ths = map SPEC_ALL (CONJUNCTS(ASSUME bod)) in
    let ths' = end_itlist (@) (map (CONJUNCTS o CONV_RULE CNF_CONV) ths) in
    let rth = PROVER9_REFUTE ths' in
    let eth = itlist SIMPLE_CHOOSE evs rth in
    let sth = PROVE_HYP (UNDISCH(fst(EQ_IMP_RULE ith))) eth in
    prule(DISCH tm' sth);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

let FRIEND_0 = time PROVER9
 `(!x:P. ~friend(x,x)) /\ ~(a:P = b) /\ (!x y. friend(x,y) ==> friend(y,x))
  ==> (!x. ?y z. friend(x,y) /\ ~friend(x,z)) \/
          (!x. ?y z. ~(y = z) /\ ~friend(x,y) /\ ~friend(x,z))`;;

let FRIEND_1 = time PROVER9
 `(!x:P. ~friend(x,x)) /\ a IN s /\ b IN s /\ ~(a:P = b) /\
  (!x y. friend(x,y) ==> friend(y,x))
  ==> (!x. x IN s ==> ?y z. y IN s /\ z IN s /\ friend(x,y) /\ ~friend(x,z)) \/
      (!x. x IN s ==> ?y z. y IN s /\ z IN s /\
                      ~(y = z) /\ ~friend(x,y) /\ ~friend(x,z))`;;

let LOS = time PROVER9
 `(!x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\
  (!x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\
  (!x y. Q(x,y) ==> Q(y,x)) /\
  (!x y. P(x,y) \/ Q(x,y)) /\
  ~P(a,b) /\ ~Q(c,d)
  ==> F`;;

let CONWAY_1 = time PROVER9
  `(!x. 0 + x = x) /\
   (!x y. x + y = y + x) /\
   (!x y z. x + (y + z) = (x + y) + z) /\
   (!x. 1 * x = x) /\ (!x. x * 1 = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x. 0 * x = 0) /\ (!x. x * 0 = 0) /\
   (!x y z. x * (y + z) = (x * y) + (x * z)) /\
   (!x y z. (x + y) * z = (x * z) + (y * z)) /\
   (!x y. star(x * y) = 1 + x * star(y * x) * y) /\
   (!x y. star(x + y) = star(star(x) * y) * star(x))
   ==> star(star(star(1))) = star(star(1))`;;

let CONWAY_2 = time PROVER9
  `(!x. 0 + x = x) /\
   (!x y. x + y = y + x) /\
   (!x y z. x + (y + z) = (x + y) + z) /\
   (!x. 1 * x = x) /\ (!x. x * 1 = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x. 0 * x = 0) /\ (!x. x * 0 = 0) /\
   (!x y z. x * (y + z) = (x * y) + (x * z)) /\
   (!x y z. (x + y) * z = (x * z) + (y * z)) /\
   (!x y. star(x * y) = 1 + x * star(y * x) * y) /\
   (!x y. star(x + y) = star(star(x) * y) * star(x))
   ==> !a. star(star(star(star(a)))) = star(star(star(a)))`;;

let ECKMAN_HILTON_1 = time PROVER9
 `(!x. 1 * x = x) /\
  (!x. x * 1 = x) /\
  (!x. 1 + x = x) /\
  (!x. x + 1 = x) /\
  (!w x y z. (w * x) + (y * z) = (w + y) * (x + z))
  ==> !a b. a * b = a + b`;;

let ECKMAN_HILTON_2 = time PROVER9
 `(!x. 1 * x = x) /\
  (!x. x * 1 = x) /\
  (!x. 1 + x = x) /\
  (!x. x + 1 = x) /\
  (!w x y z. (w * x) + (y * z) = (w + y) * (x + z))
  ==> !a b. a * b = b * a`;;

let ECKMAN_HILTON_3 = time PROVER9
 `(!x. 1 * x = x) /\
  (!x. x * 1 = x) /\
  (!x. 0 + x = x) /\
  (!x. x + 0 = x) /\
  (!w x y z. (w * x) + (y * z) = (w + y) * (x + z))
  ==> !a b. a * b = b * a`;;

let ECKMAN_HILTON_4 = time PROVER9
 `(!x. 1 * x = x) /\
  (!x. x * 1 = x) /\
  (!x. 0 + x = x) /\
  (!x. x + 0 = x) /\
  (!w x y z. (w * x) + (y * z) = (w + y) * (x + z))
  ==> !a b. a + b = a * b`;;

let DOUBLE_DISTRIB = time PROVER9
 `(!x y z. (x * y) * z = (x * z) * (y * z)) /\
  (!x y z. z * (x * y) = (z * x) * (z * y))
  ==> !a b c. (a * b) * (c * a) = (a * c) * (b * a)`;;

let MOORE_PENROSE_PSEUDOINVERSE_UNIQUE = time PROVER9
 `X * A * X = X /\ transpose(A * X) = A * X /\
  A * X * A = A /\ transpose(X * A) = X * A /\                     
  Y * A * Y = Y /\ transpose(A * Y) = A * Y /\                             
  A * Y * A = A /\ transpose(Y * A) = Y * A /\                       
  (!x y z. (x * y) * z = x * (y * z)) /\                           
  (!x y. transpose(x * y) = transpose(y) * transpose(x))      
  ==> X = Y`;;
