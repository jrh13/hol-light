(* ========================================================================= *)
(*        Miz3 interface for readable HOL Light tactics formal proofs        *)
(*                                                                           *)
(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* The primary meaning of readability is explained in the HOL Light tutorial *)
(* on page 81 after the proof of NSQRT_2 (ported below),                     *)
(* "We would like to claim that this proof can be read in isolation, without *)
(* running it in HOL.  For each step, every fact we used is clearly labelled *)
(* somewhere else in the proof, and every assumption is given explicitly."   *)
(* However readability is often improved by using tactics constructs like    *)
(* SIMP_TAC and MATCH_MP_TAC, which allow facts and assumptions to not be    *)
(* given explicitly, so as to not lose sight of the proof.  Readability is   *)
(* improved by a miz3 interface with few type annotations, back-quotes or    *)
(* double-quotes, and allowing HOL4/Isabelle math characters, e.g.           *)
(* ⇒ ⇔ ∧ ∨ ¬ ∀ ∃ ∈ ∉ α β γ λ θ μ ⊂ ∩ ∪ ∅ ━ ≡ ≅ ∡ ∥ ∏ ∘ → ◼.                  *)
(* We use ideas for readable formal proofs due to John Harrison ("Towards    *)
(* more readable proofs" of the tutorial and Examples/mizar.ml), Freek       *)
(* Wiedijk (Mizarlight/miz2a.ml, miz3/miz3.ml and arxiv.org/pdf/1201.3601    *)
(* "A Synthesis of Procedural and Declarative Styles of Interactive          *)
(* Theorem Proving"), Marco Maggesi (author of tactic constructs             *)
(* INTRO_TAC, DESTRUCT_TAC & HYP), Petros Papapanagiotou (coauthor of        *)
(* Isabelle Light), Vincent Aravantinos (author of the Q-module              *)
(* https://github.com/aravantv/HOL-Light-Q) and Mark Adams (author of HOL    *)
(* Zero and Tactician).  These readability ideas yield miz3-type             *)
(* "declarative" constructs like consider and case_split.  The semantics of  *)
(* readable.ml is clear from an obvious translation to HOL Light proofs.  An *)
(* interactive mode is useful in writing, debugging and displaying proofs.   *)
(*                                                                           *)
(* The construct "case_split" reducing the goal to various cases given by    *)
(* "suppose" clauses.  The construct "proof" [...] "qed" allows arbitrarily  *)
(* long proofs, which can be arbitrarily nested with other case_split and    *)
(* proof/qed constructs.  THENL is only implemented implicitly in case_split *)
(* (also eq_tac and conj_tac), and this requires adjustments, such as using  *)
(* MATCH_MP_TAC num_INDUCTION instead of INDUCT_TAC.                         *)
(* ========================================================================= *)

(* The Str library defines regexp functions needed to process strings.       *)

#load "str.cma";;

(* parse_qproof uses system.ml quotexpander feature designed for miz3.ml to  *)
(* turn backquoted expression `;[...]` into a string with no newline or      *)
(* backslash problems.  Note that miz3.ml defines parse_qproof differently.  *)

let parse_qproof s = (String.sub s 1 (String.length s - 1));;

(* Allows HOL4 and Isabelle style math characters.                           *)

let CleanMathFontsForHOL_Light s =
  let rec clean s loStringPairs =
    match loStringPairs with
    | [] -> s
    | hd :: tl ->
      let s = Str.global_replace (Str.regexp (fst hd)) (snd hd) s in
      clean s tl in
      clean s ["⇒","==>"; "⇔","<=>"; "∧","/\\ "; "∨","\\/"; "¬","~";
      "∀","!"; "∃","?"; "∈","IN"; "∉","NOTIN";
      "α","alpha"; "β","beta"; "γ","gamma"; "λ","\\ "; "θ","theta"; "μ","mu";
      "⊂","SUBSET"; "∩","INTER"; "∪","UNION"; "∅","{}"; "━","DELETE";
      "≡","==="; "≅","cong"; "∡","angle"; "∥","parallel";
      "∏","prod"; "∘","_o_";"→","--->"; "◼","DIFF"];;

(* printReadExn prints uncluttered error messages via Readable_fail.  This   *)
(* is due to Mark Adams, who also explained Roland Zumkeller's exec below.   *)

exception Readable_fail of string;;

let printReadExn e =
  match e with
  | Readable_fail s
       -> print_string s
  | _  -> print_string (Printexc.to_string e);;

#install_printer printReadExn;;

(* From update_database.ml: Execute any OCaml expression given as a string.  *)

let exec = ignore o Toploop.execute_phrase false Format.std_formatter
  o !Toploop.parse_toplevel_phrase o Lexing.from_string;;

(* Following miz3.ml, exec_thm returns the theorem representing a string, so *)
(* exec_thm "FORALL_PAIR_THM";; returns                                      *)
(* val it : thm = |- !P. (!p. P p) <=> (!p1 p2. P (p1,p2))                   *)
(* Extra error-checking is done to rule out the possibility of the theorem   *)
(* string ending with a semicolon.                                           *)

let thm_ref = ref TRUTH;;
let tactic_ref = ref ALL_TAC;;
let thmtactic_ref = ref MATCH_MP_TAC;;
let thmlist_tactic_ref = ref REWRITE_TAC;;
let termlist_thm_thm_ref = ref SPECL;;
let thm_thm_ref = ref GSYM;;
let term_thm_ref = ref ARITH_RULE;;
let thmlist_term_thm_ref = ref MESON;;

let exec_thm s =
  if Str.string_match (Str.regexp "[^;]*;") s 0 then raise Noparse
  else
    try exec ("thm_ref := (("^ s ^"): thm);;");
      !thm_ref
    with _ -> raise Noparse;;

let exec_tactic s =
  try exec ("tactic_ref := (("^ s ^"): tactic);;"); !tactic_ref
  with _ -> raise Noparse;;

let exec_thmlist_tactic s =
  try
    exec ("thmlist_tactic_ref := (("^ s ^"): thm list -> tactic);;");
    !thmlist_tactic_ref
  with _ -> raise Noparse;;

let exec_thmtactic s =
  try exec ("thmtactic_ref := (("^ s ^"): thm -> tactic);;"); !thmtactic_ref
  with _ -> raise Noparse;;

let exec_termlist_thm_thm s =
  try exec ("termlist_thm_thm_ref := (("^ s ^"): (term list -> thm -> thm));;");
    !termlist_thm_thm_ref
  with _ -> raise Noparse;;

let exec_thm_thm s =
  try exec ("thm_thm_ref := (("^ s ^"): (thm -> thm));;");
    !thm_thm_ref
  with _ -> raise Noparse;;

let exec_term_thm s =
  try exec ("term_thm_ref := (("^ s ^"): (term -> thm));;");
    !term_thm_ref
  with _ -> raise Noparse;;

let exec_thmlist_term_thm s =
  try exec ("thmlist_term_thm_ref := (("^ s ^"): (thm list ->term -> thm));;");
    !thmlist_term_thm_ref
  with _ -> raise Noparse;;

(* make_env and parse_env_string (following parse_term from parser.ml,       *)
(* Mizarlight/miz2a.ml and https://github.com/aravantv/HOL-Light-Q) turn a   *)
(* string into a term with types inferred by the goal and assumption list.   *)

let (make_env: goal -> (string * pretype) list) =
  fun (asl, w) -> map ((fun (s, ty) -> (s, pretype_of_type ty)) o dest_var)
                   (freesl (w::(map (concl o snd) asl)));;

let parse_env_string env s =
  let (ptm, l) = (parse_preterm o lex o explode) s in
  if l = [] then (term_of_preterm o retypecheck env) ptm
  else raise (Readable_fail
    ("Unparsed input  at the end of the term\n" ^ s));;

(* versions of new_constant, parse_as_infix, new_definition and new_axiom    *)

let NewConstant (x, y) = new_constant(CleanMathFontsForHOL_Light x, y);;

let ParseAsInfix (x, y) = parse_as_infix (CleanMathFontsForHOL_Light x, y);;

let NewDefinition s =
  new_definition (parse_env_string [] (CleanMathFontsForHOL_Light s));;

let NewAxiom s =
  new_axiom (parse_env_string [] (CleanMathFontsForHOL_Light s));;

(* String versions without type annotations of SUBGOAL_THEN, SUBGOAL_TAC,    *)
(* intro_TAC, EXISTS_TAC, X_GEN_TAC, and EXISTS_TAC, and also new miz3-type  *)
(* tactic constructs assume, raa, consider and case_split.                   *)

(* subgoal_THEN stm ttac gl = (SUBGOAL_THEN t ttac) gl,                      *)
(* where stm is a string that turned into a statement t by make_env and      *)
(* parse_env_string, using the goal gl.  We call stm a string statement.     *)
(* ttac is often the thm_tactic (LABEL_TAC string) or (DESTRUCT_TAC string). *)

let subgoal_THEN stm ttac gl =
  SUBGOAL_THEN (parse_env_string (make_env gl) stm) ttac gl;;

(* subgoal_TAC stm lab tac gl = (SUBGOAL_TAC lab t [tac]) gl,                *)
(* exists_TAC stm gl = (EXISTS_TAC t) gl, and                                *)
(* X_gen_TAC svar gl = (X_GEN_TAC v) gl, where                               *)
(* stm is a string statement which is turned into a statement t by make_env, *)
(* parse_env_string and the goal gl. Similarly string svar is turned into a  *)
(* variable v.                                                               *)
(* X_genl_TAC combines X_gen_TAC and GENL.  Since below in StepToTactic the  *)
(* string-term list uses whitespace as the delimiter and no braces, there is *)
(* no reason in readable.ml proofs to use X_gen_TAC instead X_genl_TAC.      *)
(* intro_TAC is INTRO_TAC with the delimiter ";" replaced with",".           *)
(* assume notalpha lab tac                                                   *)
(* is the tactic which, when applied to goal gl = (asl, w), with tac a proof *)
(* that w <=> x ∨ y,  makes the goal y, with the string statement notalpha   *)
(* turning into the statement ~x, using the goal gl, which is referred to by *)
(* the nonempty label lab, both in the proof tac and in the new goal y.      *)
(* eq_tac string tac                                                         *)
(* requires the goal to be an iff statement of the form x ⇔ y and then       *)
(* performs an EQ_TAC.  If string = "Right", then the tactic tac proves the  *)
(* implication y ⇒ x, and the goal becomes the other implication x ⇒ y.      *)
(* If string = "Left", then tac proves x ⇒ y and the goal becomes y ⇒ x.     *)
(* conj_tac string tac                                                       *)
(* requires the goal to be a conjunction statement x ∧ y and then performs a *)
(* CONJ_TAC.  If string = "Left" then the tactic tac proves x, and the goal  *)
(* becomes y.  If string = "Right", tac proves y and the new goal is x.      *)
(* raa stm lab tac                                                           *)
(* begins a proof by contradiction (reductio ad absurdum).  The string       *)
(* statement stm is transformed into a statement x by subgoal_THEN, and tac  *)
(* proves the goal using the added assumption ~x, labeled by the nonempty    *)
(* string lab.  If - is used by tac, it will refer to ~x.  There is a new    *)
(* subgoal F (false) which has the added assumption x, also labeled lab.     *)
(* consider svars stm lab tac                                                *)
(* defines new variables given by the string svars = "v1 v2 ... vn" and the  *)
(* string statement stm, which subgoal_THEN turns into statement t, labeled  *)
(* by lab.  The tactic tac proves the existential statement ?v1 ... vn. t.   *)
(* case_split sDestruct tac listofDisj listofTac                             *)
(* reduces the goal to n cases which are solved separately.  listofDisj is a *)
(* list of strings [st_1;...; st_n] whose disjunction st_1 \/...\/ st_n is a *)
(* string statement proved by tactic tac.  listofTac is a list of tactics    *)
(* [tac_1;...; tac_n] which prove the statements st_1,..., st_n.  The string *)
(* sDestruct must have the form "lab_1 |...| lab_n", and lab_i is a label    *)
(* used by tac_i to prove st_i.  Each lab_i must be a nonempty string.       *)

let subgoal_TAC stm lab tac gl =
  SUBGOAL_TAC lab (parse_env_string (make_env gl) stm) [tac] gl;;

let exists_TAC stm gl =
  EXISTS_TAC (parse_env_string (make_env gl) stm) gl;;

let X_gen_TAC svar (asl, w as gl) =
  let vartype = (snd o dest_var o fst o dest_forall) w in
  X_GEN_TAC (mk_var (svar, vartype)) gl;;

let X_genl_TAC svarlist = MAP_EVERY X_gen_TAC svarlist;;

let intro_TAC s = INTRO_TAC (Str.global_replace (Str.regexp ",") ";" s);;

let assume notalpha lab tac (asl, w as gl) =
  let t = parse_env_string (make_env gl) notalpha in
  let notalpha_implies_beta = mk_imp(t, mk_conj(t, w)) in
  (SUBGOAL_THEN notalpha_implies_beta (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac] THEN
  HYP REWRITE_TAC lab [MESON[] `!x y. ~x ==> (~x /\ (x \/ y) <=> y)`]) gl;;

let raa stm lab tac = subgoal_THEN (stm ^ " ==> F") (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac];;

let eq_tac string tac =
  if string = "Right" then EQ_TAC THENL [ALL_TAC; tac]
  else if string = "Left" then EQ_TAC THENL [tac; ALL_TAC]
  else raise (Readable_fail
    ("eq_tac requires " ^  string ^" to be either Left or Right"));;

let conj_tac string tac =
  if string = "Right" then CONJ_TAC THENL [ALL_TAC; tac]
  else if string = "Left" then CONJ_TAC THENL [tac; ALL_TAC]
  else raise (Readable_fail
    ("conj_tac requires " ^  string ^" to be either Left or Right"));;

let consider svars stm lab tac =
  subgoal_THEN ("?"^ svars ^ ". "^ stm)
    (DESTRUCT_TAC ("@"^ svars ^ "."^ lab)) THENL [tac; ALL_TAC];;

let case_split sDestruct tac listofDisj listofTac =
  let disjunction = itlist
    (fun s t -> if t = "" then "("^ s ^")" else "("^ s ^") \\/ "^ t)
    listofDisj "" in
  subgoal_TAC disjunction "" tac THEN
  FIRST_X_ASSUM (DESTRUCT_TAC sDestruct) THENL listofTac;;

(* Following the HOL Light tutorial section "Towards more readable proofs."  *)

let fol = MESON_TAC;;
let rewrite = REWRITE_TAC;;
let simplify = SIMP_TAC;;
let set = SET_TAC;;
let rewriteR = GEN_REWRITE_TAC (RAND_CONV);;
let rewriteRLDepth = GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o DEPTH_CONV);;
let TACtoThmTactic tac = fun  ths -> MAP_EVERY MP_TAC ths THEN tac;;
let arithmetic = TACtoThmTactic ARITH_TAC;;
let real_arithmetic = TACtoThmTactic REAL_ARITH_TAC;;
let num_ring = TACtoThmTactic (CONV_TAC NUM_RING);;
let real_ring = TACtoThmTactic (CONV_TAC REAL_RING);;

let ws = "[ \t\n]+";;
let ws0 = "[ \t\n]*";;

let StringRegexpEqual r s = Str.string_match r s 0 &&
  s = Str.matched_string s;;

(* FindMatch sleft sright s                                                  *)
(* turns strings sleft and sright into regexps, recursively searches string  *)
(* s for matched pairs of substrings matching sleft and sright, and returns  *)
(* the position after the first substring matched by sright which is not     *)
(* paired with an sleft-matching substring.  Often here sleft ends with      *)
(* whitespace (ws) while sright begins with ws.  The "degenerate" case of    *)
(* X^ws^Y where X^ws matches sleft and ws^Y matches sright is handled by     *)
(* backing up a character after an sleft match if the last character is ws.  *)

let FindMatch sleft sright s =
  let test = Str.regexp ("\("^ sleft ^"\|"^ sright ^"\)")
  and left = Str.regexp sleft in
  let rec FindMatchPosition s count =
    if count = 1 then 0
    else
      try
        ignore(Str.search_forward test s 0);
        let TestMatch = Str.matched_group 1 s
        and AfterTest = Str.match_end() in
        let LastChar = Str.last_chars (Str.string_before s AfterTest) 1 in
        let endpos =
          if Str.string_match (Str.regexp ws) LastChar 0
          then AfterTest - 1 else AfterTest in
        let rest = Str.string_after s endpos
        and increment =
          if StringRegexpEqual left TestMatch then -1 else 1 in
        endpos + (FindMatchPosition rest (count + increment))
      with Not_found -> raise (Readable_fail
        ("No matching right bracket operator "^ sright ^
        " to left bracket operator "^ sleft ^" in "^ s)) in
  FindMatchPosition s 0;;

(* FindSemicolon uses FindMatch to find the position before the next         *)
(* semicolon which is not a delimiter of a list.                             *)

let rec FindSemicolon s =
  try
    let rec FindMatchPosition s pos =
      let start = Str.search_forward (Str.regexp ";\|\[") s pos  in
      if Str.matched_string s = ";" then start
      else
        let rest = Str.string_after s (start + 1) in
        let MatchingSquareBrace = FindMatch "\[" "\]" rest in
        let newpos = start + 1 + MatchingSquareBrace in
        FindMatchPosition s newpos in
    FindMatchPosition s 0
  with Not_found -> raise (Readable_fail ("No final semicolon in "^ s));;

(* FindCases uses FindMatch to take a string                                 *)
(* "suppose" proof_1 "end;" ... "suppose" proof_n "end;"                     *)
(* and return the list [proof_1; proof_2; ... ; proof_n].                    *)

let rec FindCases s =
  let sleftCase, srightCase = ws^ "suppose"^ws, ws^ "end" ^ws0^ ";" in
  if Str.string_match (Str.regexp sleftCase) s 0 then
    let CaseEndRest = Str.string_after s (Str.match_end()) in
    let PosAfterEnd = FindMatch sleftCase srightCase CaseEndRest in
    let pos = Str.search_backward (Str.regexp srightCase)
      CaseEndRest PosAfterEnd in
    let case = Str.string_before CaseEndRest pos
    and rest = Str.string_after CaseEndRest PosAfterEnd in
    case :: (FindCases rest)
  else [];;

(* StringToList uses FindSemicolon to turns a string into the list of        *)
(* substrings delimited by the semicolons which are not captured in lists.   *)

let rec StringToList s =
  if StringRegexpEqual (Str.regexp ws0) s then [] else
  if Str.string_match (Str.regexp "[^;]*;") s 0 then
    let pos = FindSemicolon s in
    let head = Str.string_before s pos in
    head :: (StringToList (Str.string_after s (pos + 1)))
  else [s];;

(* ExtractWsStringList string = (["l1"; "l2"; ...; "ln"], rest),             *)
(* if string = ws ^ "[l1; l2; ...; ln]" ^ rest.  Raises Not_found otherwise. *)

let ExtractWsStringList string =
  if Str.string_match (Str.regexp (ws^ "\[")) string 0 then
    let listRest = Str.string_after string (Str.match_end()) in
    let RightBrace = FindMatch "\[" "\]" listRest in
    let rest = Str.string_after listRest RightBrace
    and list = Str.string_before listRest (RightBrace - 1) in
    (StringToList list, rest)
  else raise Not_found;;

(* theoremify string goal returns a pair  (thm, rest),                       *)
(* where thm is the first theorem found on string, using goal if needed, and *)
(* rest is the remainder of string.  Theoremify uses 3 helping functions:    *)
(* 1) CombTermThm_Term, which produces a combination of a term->thm          *)
(*      (e.g. ARITH_RULE) with a term,                                       *)
(* 2) CombThmlistTermThm_Thmlist_Term, which combines a thmlist->term->thm   *)
(*      (e.g. MESON) with a thmlist and a term, and                          *)
(* 3) CombTermlistThmThm_Termlist, which combines a termlist->thm->thm       *)
(*      (e.g. SPECL) with a termlist, and a thm produced by theoremify.      *)
(* Similar functions CombThmtactic_Thm and CombThmlisttactic_Thmlist are     *)
(* used below, along with theoremify, by StringToTactic.                     *)

let CombTermThm_Term word rest gl =
  let TermThm = exec_term_thm word in
  try
    let (stermlist, wsRest) = ExtractWsStringList rest in
    if length stermlist = 1 then
      let term = (parse_env_string (make_env gl)) (hd stermlist) in
      (TermThm term,  wsRest)
    else raise (Readable_fail ("term->thm "^ word
    ^" not followed by length 1 term list, but instead the list \n["^
    String.concat ";" stermlist ^"]"))
  with Not_found -> raise (Readable_fail ("term->thm "^ word
  ^" not followed by term list, but instead \n"^ rest));;

let CombThmlistTermThm_Thmlist_Term word rest gl =
  let ThmlistTermThm = exec_thmlist_term_thm word in
  try
    let (stermlist, wsTermRest) = ExtractWsStringList rest in
    let thmlist = map exec_thm stermlist in
    if Str.string_match (Str.regexp (ws^ "\[")) wsTermRest 0 then
      let termRest = Str.string_after wsTermRest (Str.match_end()) in
      let RightBrace = FindMatch "\[" "\]" termRest in
      let rest = Str.string_after termRest RightBrace
      and sterm = Str.string_before termRest (RightBrace - 1) in
      let term = parse_env_string (make_env gl) sterm in
      (ThmlistTermThm thmlist term, rest)
    else raise (Readable_fail ("thmlist->term->thm "^ word
      ^" followed by list of theorems ["^ String.concat ";" stermlist ^"]
      not followed by term in\n"^ wsTermRest))
  with Not_found -> raise (Readable_fail ("thmlist->term->thm "^ word
  ^" not followed by thm list in\n"^ rest));;

let rec theoremify string gl =
  if Str.string_match (Str.regexp (ws^ "\([^][ \t\n]+\)")) string 0 then
    let word = Str.matched_group 1 string
    and rest = Str.string_after string (Str.match_end()) in
    if word = "-" then (snd (hd (fst gl)), rest) else
    try (exec_thm word, rest)
    with _ ->
    try (assoc word (fst gl), rest)
    with _ ->
    try firstPairMult (exec_thm_thm word) (theoremify rest gl)
    with _ ->
    try CombTermThm_Term word rest gl
    with Noparse ->
    try CombThmlistTermThm_Thmlist_Term word rest gl
    with Noparse ->
    try CombTermlistThmThm_Termlist word rest gl
    with Noparse -> raise (Readable_fail ("Not a theorem:\n"^ string))
  else raise (Readable_fail ("Empty theorem:\n"^ string))
and
firstPairMult f (a, b) = (f a, b)
and
CombTermlistThmThm_Termlist word rest gl =
  let TermlistThmThm = exec_termlist_thm_thm word in
  try
    let (stermlist, WsThm) = ExtractWsStringList rest in
    let termlist = map (parse_env_string (make_env gl)) stermlist in
    firstPairMult (TermlistThmThm termlist) (theoremify WsThm gl)
  with Not_found -> raise (Readable_fail ("termlist->thm->thm "^ word
  ^"\n not followed by term list in\n"^ rest));;

let CombThmtactic_Thm step =
  if Str.string_match (Str.regexp (ws^ "\([a-zA-Z0-9_]+\)")) step 0 then
    let sthm_tactic = Str.matched_group 1 step
    and sthm = Str.string_after step (Str.match_end()) in
    let thm_tactic = exec_thmtactic sthm_tactic in
    fun gl ->
      let (thm, rest) = theoremify sthm gl in
      if rest = "" then thm_tactic thm gl
      else raise (Readable_fail ("thm_tactic "^ sthm_tactic
      ^" not followed by a theorem, but instead\n"^ sthm))
  else raise Not_found;;

let CombThmlisttactic_Thmlist step =
  let rec makeThmListAccum string list gl =
    if StringRegexpEqual (Str.regexp ws0) string then list else
    let (thm, rest) = theoremify string gl in
    makeThmListAccum rest (thm :: list) gl in
  if Str.string_match (Str.regexp (ws^ "\([a-zA-Z0-9_]+\)")) step 0 then
    let ttac = exec_thmlist_tactic (Str.matched_group 1 step)
    and LabThmString = Str.string_after step (Str.match_end()) in
    fun gl ->
      let LabThmList =  List.rev (makeThmListAccum LabThmString [] gl) in
      ttac LabThmList gl
  else raise Not_found;;

(* StringToTactic uses regexp functions from the Str library to transform a  *)
(* string into a tactic.  The allowable tactics are written in BNF form as   *)
(*                                                                           *)
(* Tactic := ALL_TAC | Tactic THEN Tactic | thm->tactic Thm |                *)
(*   one-word-tactic (e.g. ARITH_TAC) | thmlist->tactic Thm-list |           *)
(*   intro_TAC string | exists_TAC term | X_genl_TAC term-list |             *)
(*   case_split string Tactic statement-list Tactic-list |                   *)
(*   consider variable-list statement label Tactic |                         *)
(*   eq_tac (Right | Left) Tactic | conj_tac (Right | Left) Tactic |         *)
(*   (raa | assume | subgoal_TAC) statement label Tactic                     *)
(*                                                                           *)
(* Thm := theorem-name | label | - [i.e. last assumption] | thm->thm Thm |   *)
(*   term->thm term | thmlist->term->thm Thm-list term |                     *)
(*   term_list->thm->thm term-list Thm                                       *)
(*                                                                           *)
(* The string proofs allowed by StringToTactic are written in BNF form as    *)
(*                                                                           *)
(* Proof := Proof THEN Proof | case_split destruct_string ByProofQed         *)
(*   suppose statement; Proof end; ... suppose statement; Proof end; |       *)
(*   OneStepProof; | consider variable-list statement [label] ByProofQed |   *)
(*   eq_tac [Right|Left] ByProofQed | conj_tac [Right|Left] ByProofQed |     *)
(*   (raa | assume | ) statement [label] ByProofQed                          *)
(*                                                                           *)
(* OneStepProof := one-word-tactic | thm->tactic Thm | intro_TAC string |    *)
(*   exists_TAC term-string | X_genl_TAC variable-string-list |              *)
(*   thmlist->tactic Thm-list                                                *)
(*                                                                           *)
(* ByProofQed := by OneStepProof; | proof Proof Proof ...  Proof qed;        *)
(*                                                                           *)
(* theorem is a version of prove based on the miz3.ml thm, with argument     *)
(* statement ByProofQed                                                      *)

let rec StringToTactic s =
  if StringRegexpEqual (Str.regexp ws0) s then ALL_TAC
  else
    try makeCaseSplit s
    with _ ->
    let pos = FindSemicolon s in
    let step, rest = Str.string_before s pos, Str.string_after s (pos + 1) in
    try
      let tactic = StepToTactic step in
      tactic THEN StringToTactic rest
    with Not_found ->
    let (tactic, rest) = BigStepToTactic s step in
    tactic THEN StringToTactic rest
and
GetProof ByProof s =
  if ByProof = "by" then
    let pos = FindSemicolon s in
    let step, rest = Str.string_before s pos, Str.string_after s (pos + 1) in
    (StepToTactic step, rest)
  else
    let pos_after_qed = FindMatch (ws^"proof"^ws) (ws^"qed"^ws0^";") s in
    let pos = Str.search_backward (Str.regexp "qed") s pos_after_qed in
    let proof = StringToTactic (Str.string_before s pos) in
    (proof, Str.string_after s pos_after_qed)
and
makeCaseSplit s =
  if Str.string_match (Str.regexp (ws^ "case_split" ^ws^ "\([^;]+\)" ^ws^
    "\(by\|proof\)" ^ws)) s 0 then
    let sDestruct = Str.matched_group 1 s
    and (proof, rest) = GetProof (Str.matched_group 2 s)
      (Str.string_after s (Str.group_end 2))
    and SplitAtSemicolon case =
      let pos = FindSemicolon case in
      [Str.string_before case pos; Str.string_after case (pos + 1)] in
    let list2Case = map SplitAtSemicolon (FindCases rest) in
    let listofDisj = map hd list2Case
    and listofTac = map (StringToTactic o hd o tl) list2Case in
    case_split sDestruct proof listofDisj listofTac
  else raise Not_found
and
StepToTactic step =
  try
    if StringRegexpEqual (Str.regexp (ws^ "\([^ \t\n]+\)" ^ws0)) step then
      exec_tactic (Str.matched_group 1 step)
    else raise Not_found
  with _ ->
  try CombThmtactic_Thm step
  with _ ->
  try CombThmlisttactic_Thmlist step
  with _ ->
  if Str.string_match (Str.regexp (ws^ "intro_TAC" ^ws)) step 0 then
    let intro_string = Str.string_after step (Str.match_end()) in
    intro_TAC intro_string
  else if Str.string_match (Str.regexp (ws^ "exists_TAC" ^ws)) step 0 then
    let exists_string = Str.string_after step (Str.match_end()) in
    exists_TAC exists_string
  else if Str.string_match (Str.regexp (ws^ "X_genl_TAC" ^ws)) step 0 then
    let genl_string = Str.string_after step (Str.match_end()) in
    let svarlist = Str.split (Str.regexp ws) genl_string in
    X_genl_TAC svarlist
  else raise Not_found
and
BigStepToTactic s step =
  if Str.string_match (Str.regexp (ws^ "consider" ^ws^ "\(\(.\|\n\)+\)" ^ws^
    "such" ^ws^ "that" ^ws^ "\(\(.\|\n\)+\)" ^ws^ "\[\(\(.\|\n\)*\)\]" ^ws^
    "\(by\|proof\)" ^ws)) step 0 then
    let vars, t = Str.matched_group 1 step, Str.matched_group 3 step
    and lab = Str.matched_group 5 step
    and KeyWord, endKeyWord = Str.matched_group 7 step, (Str.group_end 7) in
    let (proof, rest) = GetProof KeyWord (Str.string_after s endKeyWord) in
    (consider vars t lab proof, rest)
  else
    try
      let start = Str.search_forward (Str.regexp
        (ws^ "\[\([^]]*\)\]" ^ws^ "\(by\|proof\)" ^ws)) step 0 in
      let statement = Str.string_before step start
      and lab = Str.matched_group 1 step
      and KeyWord = Str.matched_group 2 step
      and AfterWord = Str.string_after s (Str.group_end 2) in
      let (proof, rest) = GetProof KeyWord AfterWord in
      if StringRegexpEqual (Str.regexp (ws^ "eq_tac")) statement
      then (eq_tac lab proof, rest)
      else if StringRegexpEqual (Str.regexp (ws^ "conj_tac")) statement
      then (conj_tac lab proof, rest)
      else if
        Str.string_match (Str.regexp (ws^ "\(raa\|assume\)" ^ws)) statement 0
      then
        let statement = Str.string_after statement (Str.match_end()) in
        if Str.matched_group 1 step = "raa" then
          (raa statement lab proof, rest)
        else (assume statement lab proof, rest)
      else (subgoal_TAC statement lab proof, rest)
    with Not_found -> raise (Readable_fail
    ("Can't parse as a Proof:\n"^ step));;

let theorem s =
  let s = CleanMathFontsForHOL_Light s in
  try
    let start = Str.search_forward (Str.regexp
      (ws^ "proof\(" ^ws^ "\(.\|\n\)*\)" ^ws ^ "qed" ^ws0^ ";" ^ws0)) s 0 in
    let thm = Str.string_before s start
    and proof = Str.matched_group 1 s
    and rest = Str.string_after s (Str.match_end()) in
    if rest = "" then prove (parse_env_string [] thm, StringToTactic proof)
    else raise (Readable_fail
      ("Trailing garbage after the proof...qed:\n" ^ rest))
  with Not_found ->
  try
    let start = Str.search_forward (Str.regexp (ws^ "by")) s 0 in
    let thm = Str.string_before s start
    and proof = Str.string_after s (Str.match_end()) in
    try
      prove (parse_env_string [] thm, StepToTactic proof)
    with Not_found -> raise (Readable_fail ("Not a proof:\n" ^ proof))
  with Not_found -> raise (Readable_fail
    ("Missing initial \"proof\", \"by\", or final \"qed;\" in\n" ^ s));;

let interactive_goal s =
  let thm = CleanMathFontsForHOL_Light s in
  g (parse_env_string [] thm);;

let interactive_proof s =
  let proof = CleanMathFontsForHOL_Light s in
  e (StringToTactic proof);;

(* Two examples illustrating intro_TAC, eq_tac, exists_TAC MP_TAC and SPECL, *)
(* then a port of the HOL Light tutorial proof that sqrt 2 is irrational.    *)

let SKOLEM_THM_GEN = theorem `;
  ∀P R. (∀x. P x ⇒ ∃y. R x y)  ⇔  ∃f. ∀x. P x ⇒ R x (f x)

  proof
    intro_TAC ∀P R;
    eq_tac [Right]     by fol;
    intro_TAC H1;
    exists_TAC λx. @y. R x y;
    fol H1;
  qed;
`;;

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    MP_TAC SPECL [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

let NSQRT_2 = theorem `;
  ∀p q. p * p = 2 * q * q  ⇒  q = 0

  proof
    MATCH_MP_TAC num_WF;
    intro_TAC ∀p, A, ∀q, B;
    EVEN(p * p) ⇔ EVEN(2 * q * q)     [] by fol B;
    EVEN(p)     [] by fol - EVEN_DOUBLE EVEN_MULT;
    consider m such that p = 2 * m     [C] by fol - EVEN_EXISTS;
    case_split qp | pq by arithmetic;
    suppose q < p;
      q * q = 2 * m * m ⇒ m = 0     [] by fol qp A;
      num_ring - B C;
    end;
    suppose      p <= q;
      p * p <= q * q     [] by fol - LE_MULT2;
      q * q = 0     [] by arithmetic - B;
    num_ring -;
    end;
  qed;
`;;

(* The following interactive version of the above proof shows a feature of   *)
(* proof/qed and case_split/suppose.  You can evaluate an incomplete proof   *)
(* of a statement in an interactive_proof and complete the proof afterward,  *)
(* as indicated below.  The "suppose" clauses of a case_split can also be    *)
(* incomplete.  Do not include code below the incomplete proof or case_split *)
(* in an interactive_proof body, for the usual THEN vs THENL reason.         *)

interactive_goal `;∀p q. p * p = 2 * q * q  ⇒  q = 0
`;;
interactive_proof `;
    MATCH_MP_TAC num_WF;
    intro_TAC ∀p, A, ∀q, B;
    EVEN(p * p) ⇔ EVEN(2 * q * q)     [] proof  qed;
`;;
interactive_proof `;
      fol B;
`;;
interactive_proof `;
    EVEN(p)     [] by fol - EVEN_DOUBLE EVEN_MULT;
    consider m such that p = 2 * m     [C] proof fol - EVEN_EXISTS; qed;
`;;
interactive_proof `;
    case_split qp | pq by arithmetic;
    suppose q < p;
    end;
    suppose      p <= q;
    end;
`;;
interactive_proof `;
      q * q = 2 * m * m ⇒ m = 0     [] by fol qp A;
      num_ring - B C;
`;;
interactive_proof `;
      p * p <= q * q     [] by fol - LE_MULT2;
      q * q = 0     [] by arithmetic - B;
      num_ring -;
`;;
let NSQRT_2 = top_thm();;

(* An port from arith.ml uses by instead of proof...qed; in a short proof:   *)

let EXP_2 = theorem `;
  ∀n:num. n EXP 2 = n * n
  by rewrite BIT0_THM BIT1_THM EXP EXP_ADD MULT_CLAUSES ADD_CLAUSES`;;

(* An example using GSYM, ARITH_RULE, MESON and GEN_REWRITE_TAC, reproving   *)
(* the binomial theorem from sec 13.1--2 of the HOL Light tutorial.          *)

let binom = define
 `(!n. binom(n,0) = 1) /\
  (!k. binom(0,SUC(k)) = 0) /\
  (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))`;;

let BINOM_LT = theorem `;
  ∀n k. n < k  ⇒  binom(n,k) = 0

  proof
    INDUCT_TAC; INDUCT_TAC;
    rewrite binom ARITH LT_SUC LT;
    ASM_SIMP_TAC ARITH_RULE [n < k ==> n < SUC(k)] ARITH;
  qed;
`;;

let BINOMIAL_THEOREM = theorem `;
  ∀n. (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))

  proof
    ∀f n. nsum (0.. SUC n) f = f(0) + nsum (0..n) (λi. f (SUC i))     [Nsum0SUC] by simplify LE_0 ADD1 NSUM_CLAUSES_LEFT NSUM_OFFSET;
    MATCH_MP_TAC num_INDUCTION;
    simplify EXP NSUM_SING_NUMSEG binom SUB_0 MULT_CLAUSES;
    intro_TAC ∀n, nThm;
    rewrite Nsum0SUC binom RIGHT_ADD_DISTRIB NSUM_ADD_NUMSEG GSYM NSUM_LMUL ADD_ASSOC;
    rewriteR ADD_SYM;
    rewriteRLDepth SUB_SUC EXP;
    rewrite MULT_AC EQ_ADD_LCANCEL MESON [binom] [1 = binom(n, 0)] GSYM Nsum0SUC;
    simplify NSUM_CLAUSES_RIGHT ARITH_RULE [0 < SUC n  ∧  0 <= SUC n] LT BINOM_LT MULT_CLAUSES ADD_CLAUSES SUC_SUB1;
    simplify ARITH_RULE [k <= n  ⇒  SUC n - k = SUC(n - k)] EXP MULT_AC;
  qed;
`;;
