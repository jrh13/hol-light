(* ========================================================================= *)
(* Simple WHILE-language with relational semantics.                          *)
(* ========================================================================= *)

prioritize_num();;

parse_as_infix("refined",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Logical operations "lifted" to predicates, for readability.               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("AND",(20,"right"));;
parse_as_infix("OR",(16,"right"));;
parse_as_infix("IMP",(13,"right"));;
parse_as_infix("IMPLIES",(12,"right"));;

let FALSE = new_definition
  `FALSE = \x:S. F`;;

let TRUE = new_definition
  `TRUE = \x:S. T`;;

let NOT = new_definition
  `NOT p = \x:S. ~(p x)`;;

let AND = new_definition
  `p AND q = \x:S. p x /\ q x`;;

let OR = new_definition
  `p OR q = \x:S. p x \/ q x`;;

let ANDS = new_definition
  `ANDS P = \x:S. !p. P p ==> p x`;;

let ORS = new_definition
  `ORS P = \x:S. ?p. P p /\ p x`;;

let IMP = new_definition
  `p IMP q = \x:S. p x ==> q x`;;

(* ------------------------------------------------------------------------- *)
(* This one is different, corresponding to "subset".                         *)
(* ------------------------------------------------------------------------- *)

let IMPLIES = new_definition
  `p IMPLIES q <=> !x:S. p x ==> q x`;;

(* ------------------------------------------------------------------------- *)
(* Simple procedure to prove tautologies at the predicate level.             *)
(* ------------------------------------------------------------------------- *)

let PRED_TAUT =
  let tac =
    REWRITE_TAC[FALSE; TRUE; NOT; AND; OR; ANDS; ORS; IMP;
                IMPLIES; FUN_EQ_THM] THEN MESON_TAC[] in
  fun tm -> prove(tm,tac);;

(* ------------------------------------------------------------------------- *)
(* Some applications.                                                        *)
(* ------------------------------------------------------------------------- *)

let IMPLIES_TRANS = PRED_TAUT
  `!p q r. p IMPLIES q /\ q IMPLIES r ==> p IMPLIES r`;;

(* ------------------------------------------------------------------------- *)
(* Enumerated type of basic commands, and other derived commands.            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("Seq",(26,"right"));;

let command_INDUCTION,command_RECURSION = define_type
  "command = Assign (S->S)
           | Seq command command
           | Ite (S->bool) command command
           | While (S->bool) command";;

let SKIP = new_definition
  `SKIP = Assign I`;;

let ABORT = new_definition
  `ABORT = While TRUE SKIP`;;

let IF = new_definition
  `IF e c = Ite e c SKIP`;;

let DO = new_definition
  `DO c e = c Seq (While e c)`;;

let ASSERT = new_definition
  `ASSERT g = Ite g SKIP ABORT`;;

(* ------------------------------------------------------------------------- *)
(* Annotation commands, to allow insertion of loop (in)variants.             *)
(* ------------------------------------------------------------------------- *)

let AWHILE = new_definition
  `AWHILE (i:S->bool) (v:S->S->bool) (e:S->bool) c = While e c`;;

let ADO = new_definition
  `ADO (i:S->bool) (v:S->S->bool) c (e:S->bool) = DO c e`;;

(* ------------------------------------------------------------------------- *)
(* Useful properties of type constructors for commands.                      *)
(* ------------------------------------------------------------------------- *)

let command_DISTINCT =
  distinctness "command";;

let command_INJECTIVE =
  injectivity "command";;

(* ------------------------------------------------------------------------- *)
(* Relational semantics of commands.                                         *)
(* ------------------------------------------------------------------------- *)

let sem_RULES,sem_INDUCT,sem_CASES = new_inductive_definition
  `(!f s. sem(Assign f) s (f s)) /\
   (!c1 c2 s s' s''. sem(c1) s s' /\ sem(c2) s' s''
                     ==> sem(c1 Seq c2) s s'') /\
   (!e c1 c2 s s'. e s /\ sem(c1) s s' ==> sem(Ite e c1 c2) s s') /\
   (!e c1 c2 s s'. ~(e s) /\ sem(c2) s s' ==> sem(Ite e c1 c2) s s') /\
   (!e c s. ~(e s) ==> sem(While e c) s s) /\
   (!e c s s' s''. e s /\ sem(c) s s' /\ sem(While e c) s' s''
               ==> sem(While e c) s s'')`;;

(* ------------------------------------------------------------------------- *)
(* A more "denotational" view of the semantics.                              *)
(* ------------------------------------------------------------------------- *)

let SEM_ASSIGN = prove
 (`sem(Assign f) s s' <=> (s' = f s)`,
  GEN_REWRITE_TAC LAND_CONV [sem_CASES] THEN
  REWRITE_TAC[command_DISTINCT; command_INJECTIVE] THEN MESON_TAC[]);;

let SEM_SEQ = prove
 (`sem(c1 Seq c2) s s' <=> ?s''. sem c1 s s'' /\ sem c2 s'' s'`,
  GEN_REWRITE_TAC LAND_CONV [sem_CASES] THEN
  REWRITE_TAC[command_DISTINCT; command_INJECTIVE] THEN MESON_TAC[]);;

let SEM_ITE = prove
 (`sem(Ite e c1 c2) s s' <=> e s /\ sem c1 s s' \/
                             ~(e s) /\ sem c2 s s'`,
  GEN_REWRITE_TAC LAND_CONV [sem_CASES] THEN
  REWRITE_TAC[command_DISTINCT; command_INJECTIVE] THEN MESON_TAC[]);;

let SEM_SKIP = prove
 (`sem(SKIP) s s' <=> (s' = s)`,
  REWRITE_TAC[SKIP; SEM_ASSIGN; I_THM]);;

let SEM_IF = prove
 (`sem(IF e c) s s' <=> e s /\ sem c s s' \/ ~(e s) /\ (s = s')`,
  REWRITE_TAC[IF; SEM_ITE; SEM_SKIP; EQ_SYM_EQ]);;

let SEM_WHILE = prove
 (`sem(While e c) s s' <=> sem(IF e (c Seq While e c)) s s'`,
  GEN_REWRITE_TAC LAND_CONV [sem_CASES] THEN
  REWRITE_TAC[FUN_EQ_THM; SEM_IF; SEM_SEQ] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[command_DISTINCT; command_INJECTIVE] THEN MESON_TAC[]);;

let SEM_ABORT = prove
 (`sem(ABORT) s s' <=> F`,
  let lemma = prove
   (`!c s s'. sem c s s' ==> ~(c = ABORT)`,
    MATCH_MP_TAC sem_INDUCT THEN
    REWRITE_TAC[command_DISTINCT; command_INJECTIVE; ABORT] THEN
    REWRITE_TAC[FUN_EQ_THM; TRUE] THEN MESON_TAC[]) in
  MESON_TAC[lemma]);;

let SEM_DO = prove
 (`sem(DO c e) s s' <=> sem(c Seq IF e (DO c e)) s s'`,
  REWRITE_TAC[DO; SEM_SEQ; GSYM SEM_WHILE]);;

let SEM_ASSERT = prove
 (`sem(ASSERT g) s s' <=> g s /\ (s' = s)`,
  REWRITE_TAC[ASSERT; SEM_ITE; SEM_SKIP; SEM_ABORT]);;

(* ------------------------------------------------------------------------- *)
(* Proofs that all commands are deterministic.                               *)
(* ------------------------------------------------------------------------- *)

let deterministic = new_definition
  `deterministic r <=> !s s1 s2. r s s1 /\ r s s2 ==> (s1 = s2)`;;

let DETERMINISM = prove
 (`!c:(S)command. deterministic(sem c)`,
  REWRITE_TAC[deterministic] THEN SUBGOAL_THEN
   `!c s s1. sem c s s1 ==> !s2:S. sem c s s2 ==> (s1 = s2)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC sem_INDUCT THEN CONJ_TAC THENL
   [ALL_TAC; REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[sem_CASES] THEN
  REWRITE_TAC[command_DISTINCT; command_INJECTIVE] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Termination, weakest liberal precondition and weakest precondition.       *)
(* ------------------------------------------------------------------------- *)

let terminates = new_definition
  `terminates c s <=> ?s'. sem c s s'`;;

let wlp = new_definition
  `wlp c q s <=> !s'. sem c s s' ==> q s'`;;

let wp = new_definition
  `wp c q s <=> terminates c s /\ wlp c q s`;;

(* ------------------------------------------------------------------------- *)
(* Dijkstra's healthiness conditions (the last because of determinism).      *)
(* ------------------------------------------------------------------------- *)

let WP_TOTAL = prove
 (`!c. (wp c FALSE = FALSE)`,
  REWRITE_TAC[FUN_EQ_THM; wp; wlp; terminates; FALSE] THEN MESON_TAC[]);;

let WP_MONOTONIC = prove
 (`q IMPLIES r ==> wp c q IMPLIES wp c r`,
  REWRITE_TAC[IMPLIES; wp; wlp; terminates] THEN MESON_TAC[]);;

let WP_CONJUNCTIVE = prove
 (`(wp c q) AND (wp c r) = wp c (q AND r)`,
  REWRITE_TAC[FUN_EQ_THM; wp; wlp; terminates; AND] THEN MESON_TAC[]);;

let WP_DISJUNCTIVE = prove
 (`(wp c p) OR (wp c q) = wp c (p OR q)`,
  REWRITE_TAC[FUN_EQ_THM; wp; wlp; OR; terminates] THEN
  MESON_TAC[REWRITE_RULE[deterministic] DETERMINISM]);;

(* ------------------------------------------------------------------------- *)
(* Weakest preconditions for the primitive and derived commands.             *)
(* ------------------------------------------------------------------------- *)

let WP_ASSIGN = prove
 (`!f q. wp (Assign f) q = q o f`,
  REWRITE_TAC[wp; wlp; terminates; o_THM; FUN_EQ_THM; SEM_ASSIGN] THEN
  MESON_TAC[]);;

let WP_SEQ = prove
 (`!c1 c2 q. wp (c1 Seq c2) q = wp c1 (wp c2 q)`,
  REWRITE_TAC[wp; wlp; terminates; SEM_SEQ; FUN_EQ_THM] THEN
  MESON_TAC[REWRITE_RULE[deterministic] DETERMINISM]);;

let WP_ITE = prove
 (`!e c1 c2 q. wp (Ite e c1 c2) q = (e AND wp c1 q) OR (NOT e AND wp c2 q)`,
  REWRITE_TAC[wp; wlp; terminates; SEM_ITE; FUN_EQ_THM; AND; OR; NOT] THEN
  MESON_TAC[]);;

let WP_WHILE = prove
 (`!e c. wp (IF e (c Seq While e c)) q = wp (While e c) q`,
  REWRITE_TAC[FUN_EQ_THM; wp; wlp; terminates; GSYM SEM_WHILE]);;

let WP_SKIP = prove
 (`!q. wp SKIP q = q`,
  REWRITE_TAC[FUN_EQ_THM; SKIP; WP_ASSIGN; I_THM; o_THM]);;

let WP_ABORT = prove
 (`!q. wp ABORT q = FALSE`,
  REWRITE_TAC[FUN_EQ_THM; wp; wlp; terminates; SEM_ABORT; FALSE]);;

let WP_IF = prove
 (`!e c q. wp (IF e c) q = (e AND wp c q) OR (NOT e AND q)`,
  REWRITE_TAC[IF; WP_ITE; WP_SKIP]);;

let WP_DO = prove
 (`!e c. wp (c Seq IF e (DO c e)) q = wp (DO c e) q`,
  REWRITE_TAC[FUN_EQ_THM; wp; wlp; terminates; GSYM SEM_DO]);;

let WP_ASSERT = prove
 (`!g q. wp (ASSERT g) q = g AND q`,
  REWRITE_TAC[wp; wlp; terminates; SEM_ASSERT; FUN_EQ_THM; AND] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Rules for total correctness.                                              *)
(* ------------------------------------------------------------------------- *)

let correct = new_definition
  `correct p c q <=> p IMPLIES (wp c q)`;;

let CORRECT_PRESTRENGTH = prove
 (`!p p' c q. p IMPLIES p' /\ correct p' c q ==> correct p c q`,
  REWRITE_TAC[correct; IMPLIES_TRANS]);;

let CORRECT_POSTWEAK = prove
 (`!p c q q'. correct p c q' /\ q' IMPLIES q ==> correct p c q`,
  REWRITE_TAC[correct] THEN MESON_TAC[WP_MONOTONIC; IMPLIES_TRANS]);;

let CORRECT_ASSIGN = prove
 (`!p f q. (p IMPLIES (\s. q(f s))) ==> correct p (Assign f) q`,
  REWRITE_TAC[correct; WP_ASSIGN; IMPLIES; o_THM]);;

let CORRECT_SEQ = prove
 (`!p q r c1 c2.
        correct p c1 r /\ correct r c2 q ==> correct p (c1 Seq c2) q`,
  REWRITE_TAC[correct; WP_SEQ; o_THM] THEN
  MESON_TAC[WP_MONOTONIC; IMPLIES_TRANS]);;

let CORRECT_ITE = prove
 (`!p e c1 c2 q.
       correct (p AND e) c1 q /\ correct (p AND (NOT e)) c2 q
       ==> correct p (Ite e c1 c2) q`,
  REWRITE_TAC[correct; WP_ITE; AND; NOT; IMPLIES; OR] THEN MESON_TAC[]);;

let CORRECT_WHILE = prove
 (`! (<<) p c q e invariant.
       WF(<<) /\
       p IMPLIES invariant /\
       (NOT e) AND invariant IMPLIES q /\
       (!X:S. correct
              (invariant AND e AND (\s. X = s)) c (invariant AND (\s. s << X)))
       ==> correct p (While e c) q`,
  REWRITE_TAC[correct; IMPLIES; IN; AND; NOT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s:S. invariant s ==> wp (While e c) q s` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[WF_IND]) THEN
  X_GEN_TAC `s:S` THEN REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM WP_WHILE] THEN
  REWRITE_TAC[WP_IF; WP_SEQ; AND; OR; NOT; o_THM] THEN
  ASM_CASES_TAC `(e:S->bool) s` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `wp c (\x:S. invariant x /\ x << s) (s:S) :bool` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:S. invariant x /\ x << (s:S)) IMPLIES wp (While e c) q`
  MP_TAC THENL [REWRITE_TAC[IMPLIES] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MESON_TAC[WP_MONOTONIC; IMPLIES]);;

let CORRECT_SKIP = prove
 (`!p q. (p IMPLIES q) ==> correct p SKIP q`,
  REWRITE_TAC[correct; WP_SKIP]);;

let CORRECT_ABORT = prove
 (`!p q. F ==> correct p ABORT q`,
  REWRITE_TAC[]);;

let CORRECT_IF = prove
 (`!p e c q.
        correct (p AND e) c q /\ (p AND (NOT e)) IMPLIES q
        ==> correct p (IF e c) q`,
  REWRITE_TAC[correct; WP_IF; AND; NOT; IMPLIES; OR] THEN MESON_TAC[]);;

let CORRECT_DO = prove
 (`! (<<) p q c invariant.
        WF(<<) /\
        (e AND invariant) IMPLIES p /\
        ((NOT e) AND invariant) IMPLIES q /\
        (!X:S. correct
               (p AND (\s. X = s)) c (invariant AND (\s. s << X)))
        ==> correct p (DO c e) q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DO] THEN
  MATCH_MP_TAC CORRECT_SEQ THEN EXISTS_TAC `invariant:S->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[correct; GSYM WP_CONJUNCTIVE] THEN
    REWRITE_TAC[AND; IMPLIES] THEN MESON_TAC[];
    MATCH_MP_TAC CORRECT_WHILE THEN
    MAP_EVERY EXISTS_TAC [`(<<) :S->S->bool`; `invariant:S->bool`] THEN
    ASM_REWRITE_TAC[IMPLIES] THEN X_GEN_TAC `X:S` THEN
    MATCH_MP_TAC CORRECT_PRESTRENGTH THEN
    EXISTS_TAC `p AND (\s:S. X = s)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:S->bool) AND invariant IMPLIES p` THEN
    REWRITE_TAC[AND; IMPLIES] THEN MESON_TAC[]]);;

let CORRECT_ASSERT = prove
 (`!p g q. p IMPLIES (g AND q) ==> correct p (ASSERT g) q`,
  REWRITE_TAC[correct; WP_ASSERT]);;

(* ------------------------------------------------------------------------- *)
(* VCs for the basic commands (in fact only assign should be needed).        *)
(* ------------------------------------------------------------------------- *)

let VC_ASSIGN = prove
 (`p IMPLIES (q o f) ==> correct p (Assign f) q`,
  REWRITE_TAC[o_DEF; CORRECT_ASSIGN]);;

let VC_SKIP = prove
 (`p IMPLIES q ==> correct p SKIP q`,
  REWRITE_TAC[CORRECT_SKIP]);;

let VC_ABORT = prove
 (`F ==> correct p ABORT q`,
  MATCH_ACCEPT_TAC CORRECT_ABORT);;

let VC_ASSERT = prove
 (`p IMPLIES (b AND q) ==> correct p (ASSERT b) q`,
  REWRITE_TAC[CORRECT_ASSERT]);;

(* ------------------------------------------------------------------------- *)
(* VCs for composite commands other than sequences.                          *)
(* ------------------------------------------------------------------------- *)

let VC_ITE = prove
 (`correct (p AND e) c1 q /\ correct (p AND NOT e) c2 q
   ==> correct p (Ite e c1 c2) q`,
  REWRITE_TAC[CORRECT_ITE]);;

let VC_IF = prove
 (`correct (p AND e) c q /\ p AND NOT e IMPLIES q
   ==> correct p (IF e c) q`,
  REWRITE_TAC[CORRECT_IF]);;

let VC_AWHILE_VARIANT = prove
 (`WF(<<) /\
   p IMPLIES invariant /\
   (NOT e) AND invariant IMPLIES q /\
   (!X. correct
        (invariant AND e AND (\s. X = s)) c (invariant AND (\s. s << X)))
   ==> correct p (AWHILE invariant (<<) e c) q`,
  REWRITE_TAC[AWHILE; CORRECT_WHILE]);;

let VC_AWHILE_MEASURE = prove
 (`p IMPLIES invariant /\
   (NOT e) AND invariant IMPLIES q /\
   (!X. correct
          (invariant AND e AND (\s:S. X = m(s)))
          c
          (invariant AND (\s. m(s) < X)))
   ==> correct p (AWHILE invariant (MEASURE m) e c) q`,
  STRIP_TAC THEN MATCH_MP_TAC VC_AWHILE_VARIANT THEN
  ASM_REWRITE_TAC[WF_MEASURE] THEN
  X_GEN_TAC `X:S` THEN FIRST_ASSUM(MP_TAC o SPEC `(m:S->num) X`) THEN
  REWRITE_TAC[correct; AND; IMPLIES; MEASURE] THEN MESON_TAC[]);;

let VC_ADO_VARIANT = prove
 (`WF(<<) /\
   (e AND invariant) IMPLIES p /\
   ((NOT e) AND invariant) IMPLIES q /\
   (!X. correct
          (p AND (\s. X = s)) c (invariant AND (\s. s << X)))
   ==> correct p (ADO invariant (<<) c e) q`,
  REWRITE_TAC[ADO; CORRECT_DO]);;

let VC_ADO_MEASURE = prove
 (`(e AND invariant) IMPLIES p /\
   ((NOT e) AND invariant) IMPLIES q /\
   (!X. correct
          (p AND (\s:S. X = m(s))) c (invariant AND (\s. m(s) < X)))
   ==> correct p (ADO invariant (MEASURE m) c e) q`,
  STRIP_TAC THEN MATCH_MP_TAC VC_ADO_VARIANT THEN
  ASM_REWRITE_TAC[WF_MEASURE] THEN
  X_GEN_TAC `X:S` THEN FIRST_ASSUM(MP_TAC o SPEC `(m:S->num) X`) THEN
  REWRITE_TAC[correct; AND; IMPLIES; MEASURE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* VCs for sequences of commands, using intelligence where possible.         *)
(* ------------------------------------------------------------------------- *)

let VC_SEQ_ASSERT_LEFT = prove
 (`p IMPLIES b /\ correct b c q ==> correct p (ASSERT b Seq c) q`,
  MESON_TAC[CORRECT_SEQ; CORRECT_ASSERT; CORRECT_PRESTRENGTH;
    PRED_TAUT `(p IMPLIES b) ==> (p IMPLIES b AND p)`]);;

let VC_SEQ_ASSERT_RIGHT = prove
 (`correct p c b /\ b IMPLIES q ==> correct p (c Seq (ASSERT b)) q`,
  MESON_TAC[CORRECT_SEQ; CORRECT_ASSERT;
    PRED_TAUT `(p IMPLIES b) ==> (p IMPLIES p AND b)`]);;

let VC_SEQ_ASSERT_MIDDLE = prove
 (`correct p c b /\ correct b c' q
   ==> correct p (c Seq (ASSERT b) Seq c') q`,
  MESON_TAC[CORRECT_SEQ; CORRECT_ASSERT; PRED_TAUT `b IMPLIES b AND b`]);;

let VC_SEQ_ASSIGN_LEFT = prove
 (`(p o f = p) /\ (f o f = f) /\
   correct (p AND (\s:S. s = f s)) c q
   ==> correct p ((Assign f) Seq c) q`,
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC CORRECT_SEQ THEN EXISTS_TAC `p AND (\s:S. s = f s)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VC_ASSIGN THEN
  ASM_REWRITE_TAC[IMPLIES; AND; o_THM]);;

let VC_SEQ_ASSIGN_RIGHT = prove
 (`correct p c (q o f) ==> correct p (c Seq (Assign f)) q`,
  MESON_TAC[CORRECT_SEQ; VC_ASSIGN; PRED_TAUT `(p:S->bool) IMPLIES p`]);;

(* ------------------------------------------------------------------------- *)
(* Parser for correctness assertions.                                        *)
(* ------------------------------------------------------------------------- *)

let rec dive_to_var ptm =
  match ptm with
    Varp(_,_) as vp -> vp | Typing(t,_) -> dive_to_var t | _ -> fail();;

let reserve_program_words,unreserve_program_words =
  let words = ["var"; "end"; "skip"; "abort";
               ":="; "if"; "then"; "else"; "while"; "do"] in
  (fun () -> reserve_words words),
  (fun () -> unreserve_words words);;

reserve_program_words();;

let parse_program,parse_program_assertion =
  let assign_ptm = Varp("Assign",dpty)
  and seq_ptm = Varp("Seq",dpty)
  and ite_ptm = Varp("Ite",dpty)
  and while_ptm = Varp("While",dpty)
  and skip_ptm = Varp("SKIP",dpty)
  and abort_ptm = Varp("ABORT",dpty)
  and if_ptm = Varp("IF",dpty)
  and do_ptm = Varp("DO",dpty)
  and assert_ptm = Varp("ASSERT",dpty)
  and awhile_ptm = Varp("AWHILE",dpty)
  and ado_ptm = Varp("ADO",dpty) in
  let pmk_pair(ptm1,ptm2) = Combp(Combp(Varp(",",dpty),ptm1),ptm2) in
  let varname ptm =
    match dive_to_var ptm with Varp(n,_) -> n | _ -> fail() in
  let rec assign s v e =
    match s with
      Combp(Combp(pop,lptm),rptm) ->
        if varname pop = "," then
          Combp(Combp(pop,assign lptm v e),assign rptm v e)
        else fail()
    | _ -> if varname s = v then e else s in
  let lmk_assign s v e = Combp(assign_ptm,Absp(s,assign s v e))
  and lmk_seq c cs =
    if cs = [] then c else Combp(Combp(seq_ptm,c),hd cs)
  and lmk_ite e c1 c2 = Combp(Combp(Combp(ite_ptm,e),c1),c2)
  and lmk_while e c = Combp(Combp(while_ptm,e),c)
  and lmk_skip _ = skip_ptm
  and lmk_abort _ = abort_ptm
  and lmk_if e c = Combp(Combp(if_ptm,e),c)
  and lmk_do c e = Combp(Combp(do_ptm,c),e)
  and lmk_assert e = Combp(assert_ptm,e)
  and lmk_awhile i v e c = Combp(Combp(Combp(Combp(awhile_ptm,i),v),e),c)
  and lmk_ado i v c e = Combp(Combp(Combp(Combp(ado_ptm,i),v),c),e) in
  let lmk_gwhile al e c =
    if al = [] then lmk_while e c
    else lmk_awhile (fst(hd al)) (snd(hd al)) e c
  and lmk_gdo al c e =
    if al = [] then lmk_do c e
    else lmk_ado (fst(hd al)) (snd(hd al)) c e in
  let expression s = parse_preterm >> (fun p -> Absp(s,p)) in
  let identifier =
      function ((Ident n)::rest) -> n,rest
        | _ -> raise Noparse in
  let variant s =
     (a (Ident "variant") ++ parse_preterm
      >> snd)
  ||| (a (Ident "measure") ++ expression s
       >> fun (_,m) -> Combp(Varp("MEASURE",dpty),m)) in
  let annotation s =
      a (Resword "[") ++ a (Ident "invariant") ++ expression s ++
      a (Resword ";") ++ variant s ++ a (Resword "]")
  >> fun (((((_,_),i),_),v),_) -> (i,v) in
  let rec command s i =
   (   (a (Resword "(") ++ commands s ++ a (Resword ")")
       >> (fun ((_,c),_) -> c))
    ||| (a (Resword "skip")
         >> lmk_skip)
    ||| (a (Resword "abort")
         >> lmk_abort)
    ||| (a (Resword "if") ++ expression s ++ a (Resword "then") ++ command s ++
         possibly (a (Resword "else") ++ command s >> snd)
         >> (fun ((((_,e),_),c),cs) -> if cs = [] then lmk_if e c
                                       else lmk_ite e c (hd cs)))
    ||| (a (Resword "while") ++ expression s ++ a (Resword "do") ++
                                possibly (annotation s) ++ command s
         >> (fun ((((_,e),_),al),c) -> lmk_gwhile al e c))
    ||| (a (Resword "do") ++ possibly (annotation s) ++
                             command s ++ a (Resword "while") ++ expression s
         >> (fun ((((_,al),c),_),e) -> lmk_gdo al c e))
    ||| (a (Resword "{") ++ expression s ++ a (Resword "}")
         >> (fun ((_,e),_) -> lmk_assert e))
    ||| (identifier ++ a (Resword ":=") ++ parse_preterm
         >> (fun ((v,_),e) -> lmk_assign s v e))) i
  and commands s i =
      (command s ++ possibly (a (Resword ";") ++ commands s >> snd)
       >> (fun (c,cs) -> lmk_seq c cs)) i in
  let program i =
    let ((_,s),_),r =
      (a (Resword "var") ++ parse_preterm ++ a (Resword ";")) i in
    let c,r' = (commands s ++ a (Resword "end") >> fst) r in
    (s,c),r' in
  let assertion =
    a (Ident "correct") ++ parse_preterm ++ program ++ parse_preterm
    >> fun (((_,p),(s,c)),q) ->
        Combp(Combp(Combp(Varp("correct",dpty),Absp(s,p)),c),Absp(s,q)) in
  (program >> snd),assertion;;

(* ------------------------------------------------------------------------- *)
(* Introduce the variables in the VCs.                                       *)
(* ------------------------------------------------------------------------- *)

let STATE_GEN_TAC =
  let PAIR_CONV = REWR_CONV(GSYM PAIR) in
  let rec repair vs v acc =
    try let l,r = dest_pair vs in
        let th = PAIR_CONV v in
        let tm = rand(concl th) in
        let rtm = rator tm in
        let lth,acc1 = repair l (rand rtm) acc in
        let rth,acc2 = repair r (rand tm) acc1 in
        TRANS th (MK_COMB(AP_TERM (rator rtm) lth,rth)),acc2
    with Failure _ -> REFL v,((v,vs)::acc) in
  fun (asl,w) ->
    let abstm = find_term (fun t -> not (is_abs t) && is_gabs t) w in
    let vs = fst(dest_gabs abstm) in
    let v = genvar(type_of(fst(dest_forall w))) in
    let th,gens = repair vs v [] in
    (X_GEN_TAC v THEN SUBST1_TAC th THEN
     MAP_EVERY SPEC_TAC gens THEN REPEAT GEN_TAC) (asl,w);;

let STATE_GEN_TAC' =
  let PAIR_CONV = REWR_CONV(GSYM PAIR) in
  let rec repair vs v acc =
    try let l,r = dest_pair vs in
        let th = PAIR_CONV v in
        let tm = rand(concl th) in
        let rtm = rator tm in
        let lth,acc1 = repair l (rand rtm) acc in
        let rth,acc2 = repair r (rand tm) acc1 in
        TRANS th (MK_COMB(AP_TERM (rator rtm) lth,rth)),acc2
    with Failure _ -> REFL v,((v,vs)::acc) in
  fun (asl,w) ->
    let abstm = find_term (fun t -> not (is_abs t) && is_gabs t) w in
    let vs0 = fst(dest_gabs abstm) in
    let vl0 = striplist dest_pair vs0 in
    let vl = map (variant (variables (list_mk_conj(w::map (concl o snd) asl))))
                 vl0 in
    let vs = end_itlist (curry mk_pair) vl in
    let v = genvar(type_of(fst(dest_forall w))) in
    let th,gens = repair vs v [] in
    (X_GEN_TAC v THEN SUBST1_TAC th THEN
     MAP_EVERY SPEC_TAC gens THEN REPEAT GEN_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Tidy up a verification condition.                                         *)
(* ------------------------------------------------------------------------- *)

let VC_UNPACK_TAC =
  REWRITE_TAC[IMPLIES; o_THM; FALSE; TRUE; AND; OR; NOT; IMP] THEN
  STATE_GEN_TAC THEN CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC];;

(* ------------------------------------------------------------------------- *)
(* Calculate a (pseudo-) weakest precondition for command.                   *)
(* ------------------------------------------------------------------------- *)

let find_pwp =
  let wptms =
    (map (snd o strip_forall o concl)
         [WP_ASSIGN; WP_ITE; WP_SKIP; WP_ABORT; WP_IF; WP_ASSERT]) @
    [`wp (AWHILE i v e c) q = i`; `wp (ADO i v c e) q = i`] in
  let conv tm =
    tryfind (fun t -> rand (instantiate (term_match [] (lhand t) tm) t))
            wptms in
  fun tm q -> conv(mk_comb(list_mk_icomb "wp" [tm],q));;

(* ------------------------------------------------------------------------- *)
(* Tools for automatic VC generation from annotated program.                 *)
(* ------------------------------------------------------------------------- *)

let VC_SEQ_TAC =
  let is_seq = is_binary "Seq"
  and strip_seq = striplist (dest_binary "Seq")
  and is_assert tm =
    try fst(dest_const(rator tm)) = "ASSERT" with Failure _ -> false
  and is_assign tm =
     try fst(dest_const(rator tm)) = "Assign" with Failure _ -> false
  and SIDE_TAC =
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN STATE_GEN_TAC THEN
    PURE_REWRITE_TAC[IMPLIES; o_THM; FALSE; TRUE; AND; OR; NOT; IMP] THEN
    CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN NO_TAC in
  let ADJUST_TAC ptm ptm' ((_,w) as gl) =
    let w' = subst [ptm',ptm] w in
    let th = EQT_ELIM(REWRITE_CONV[correct; WP_SEQ] (mk_eq(w,w'))) in
    GEN_REWRITE_TAC I [th] gl in
  fun (asl,w) ->
    let cptm,q = dest_comb w in
    let cpt,ptm = dest_comb cptm in
    let ctm,p = dest_comb cpt in
    let ptms = strip_seq ptm in
    let seq = rator(rator ptm) in
    try let atm = find is_assert ptms in
        let i = index atm ptms in
        if i = 0 then
          let ptm' = mk_binop seq (hd ptms) (list_mk_binop seq (tl ptms)) in
          (ADJUST_TAC ptm ptm' THEN
           MATCH_MP_TAC VC_SEQ_ASSERT_LEFT THEN CONJ_TAC THENL
            [VC_UNPACK_TAC; ALL_TAC]) (asl,w)
        else if i = length ptms - 1 then
          let ptm' = mk_binop seq (list_mk_binop seq (butlast ptms))
                                  (last ptms) in
          (ADJUST_TAC ptm ptm' THEN
           MATCH_MP_TAC VC_SEQ_ASSERT_RIGHT THEN CONJ_TAC THENL
            [ALL_TAC; VC_UNPACK_TAC]) (asl,w)
        else
          let l,mr = chop_list (index atm ptms) ptms in
          let ptm' = mk_binop seq (list_mk_binop seq l)
                       (mk_binop seq (hd mr) (list_mk_binop seq (tl mr))) in
          (ADJUST_TAC ptm ptm' THEN
           MATCH_MP_TAC VC_SEQ_ASSERT_MIDDLE THEN CONJ_TAC) (asl,w)
    with Failure "find" -> try
        if is_assign (hd ptms) then
          let ptm' = mk_binop seq (hd ptms) (list_mk_binop seq (tl ptms)) in
          (ADJUST_TAC ptm ptm' THEN
           MATCH_MP_TAC VC_SEQ_ASSIGN_LEFT THEN REPEAT CONJ_TAC THENL
            [SIDE_TAC; SIDE_TAC; ALL_TAC]) (asl,w)
        else fail()
    with Failure _ ->
        let ptm' = mk_binop seq
          (list_mk_binop seq (butlast ptms)) (last ptms) in
        let pwp = find_pwp (rand ptm') q in
        (ADJUST_TAC ptm ptm' THEN MATCH_MP_TAC CORRECT_SEQ THEN
         EXISTS_TAC pwp THEN CONJ_TAC)
        (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Tactic to apply a 1-step VC generation.                                   *)
(* ------------------------------------------------------------------------- *)

let VC_STEP_TAC =
  let tacnet =
  itlist (enter [])
   [`correct p SKIP q`,
    MATCH_MP_TAC VC_SKIP THEN VC_UNPACK_TAC;
    `correct p (ASSERT b) q`,
    MATCH_MP_TAC VC_ASSERT THEN VC_UNPACK_TAC;
    `correct p (Assign f) q`,
    MATCH_MP_TAC VC_ASSIGN THEN VC_UNPACK_TAC;
    `correct p (Ite e c1 c2) q`,
    MATCH_MP_TAC VC_ITE THEN CONJ_TAC;
    `correct p (IF e c) q`,
    MATCH_MP_TAC VC_IF THEN CONJ_TAC THENL [ALL_TAC; VC_UNPACK_TAC];
    `correct p (AWHILE i (MEASURE m) e c) q`,
    MATCH_MP_TAC VC_AWHILE_MEASURE THEN REPEAT CONJ_TAC THENL
       [VC_UNPACK_TAC; VC_UNPACK_TAC; GEN_TAC];
    `correct p (AWHILE i v e c) q`,
    MATCH_MP_TAC VC_AWHILE_VARIANT THEN REPEAT CONJ_TAC THENL
       [ALL_TAC; VC_UNPACK_TAC; VC_UNPACK_TAC; STATE_GEN_TAC'];
    `correct p (ADO i (MEASURE m) c e) q`,
    MATCH_MP_TAC VC_ADO_MEASURE THEN REPEAT CONJ_TAC THENL
       [VC_UNPACK_TAC; VC_UNPACK_TAC; STATE_GEN_TAC'];
    `correct p (ADO i v c e) q`,
    MATCH_MP_TAC VC_ADO_VARIANT THEN REPEAT CONJ_TAC THENL
       [ALL_TAC; VC_UNPACK_TAC; VC_UNPACK_TAC; STATE_GEN_TAC'];
    `correct p (c1 Seq c2) q`,
    VC_SEQ_TAC] empty_net in
  fun (asl,w) -> FIRST(lookup w tacnet) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Final packaging to strip away the program completely.                     *)
(* ------------------------------------------------------------------------- *)

let VC_TAC = REPEAT VC_STEP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Some examples.                                                            *)
(* ------------------------------------------------------------------------- *)

install_parser ("correct",parse_program_assertion);;

let EXAMPLE_FACTORIAL = prove
 (`correct
   T
     var x,y,n;
       x := 0;
       y := 1;
       while x < n do [invariant x <= n /\ (y = FACT x); measure n - x]
        (x := x + 1;
         y := y * x)
     end
   y = FACT n`,
  VC_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[FACT; LE_0];
    REWRITE_TAC[CONJ_ASSOC; NOT_LT; LE_ANTISYM] THEN MESON_TAC[];
    REWRITE_TAC[GSYM ADD1; FACT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MULT_AC] THEN UNDISCH_TAC `x < n` THEN ARITH_TAC]);;

delete_parser "correct";;
