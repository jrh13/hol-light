(* ========================================================================= *)
(* Miz3 interface for tactics proof, allowing readable formal proofs,        *)
(* improving on miz3 mainly by allowing full use of REWRITE_TAC.             *)
(*                                                                           *)
(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* We use ideas for readable formal proofs due to John Harrison ("Towards    *)
(* more readable proofs" of the tutorial and Examples/mizar.ml), Freek       *)
(* Wiedijk (Mizarlight/miz2a.ml, miz3/miz3.ml and arxiv.org/pdf/1201.3601    *)
(* "A Synthesis of Procedural and Declarative Styles of Interactive          *)
(* Theorem Proving"), Marco Maggesi (author of tactic constructs             *)
(* INTRO_TAC, DESTRUCT_TAC & HYP), Petros Papapanagiotou (coauthor of        *)
(* Isabelle Light), Vincent Aravantinos (author of the Q-module              *)
(* https://github.com/aravantv/HOL-Light-Q) and Mark Adams (author of HOL    *)
(* Zero and Tactician).  These readability ideas yield miz3-type             *)
(* "declarative" constructs like consider and case_split, and also a         *)
(* miz3-type uncluttered interface, with few type annotations, backquotes or *)
(* double quotes. Many math characters can be used, as in Isabelle and HOL4: *)
(* ⇒ ⇔ ∧ ∨ ¬ ∀ ∃ ∈ ∉ α β γ λ θ μ ⊂ ∩ ∪ ∅ ━ ≡ ≅ ∡ ∥ ∏ ∘ →.               *)
(* The semantics of readable.ml is clear from the obvious translation to HOL *)
(* Light tactics proofs.  As in HOL Light, there is an interactive mode      *)
(* which is similarly useful in writing and debugging proofs.                *)
(*                                                                           *)
(* The construct "case_split" reducing the goal to various cases, each given *)
(* by a "suppose" clause.  The construct "proof" [...] "qed" allows          *)
(* arbitrarily long proofs, which can be arbitrarily nested with other       *)
(* case_split and proof/qed constructs.  THENL is not implemented, except    *)
(* implicitly in case_split, to encourage readable proof, but it would be    *)
(* easy to implement.  The lack of THENL requires adjustments, such as using *)
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
      "∏","prod"; "∘","_o_";"→","--->"];;

(* printReadExn prints uncluttered error messages via Readable_fail.  This   *) (* is due to Mark Adams, who also explained Roland Zumkeller's exec below.   *)

exception Readable_fail of string;;

let printReadExn e =
  match e with
  | Readable_fail s
       -> print_string s
  | _  -> print_string (Printexc.to_string e);;

#install_printer printReadExn;;

(* From update_database.ml: Execute any OCaml expression given as a string. *)

let exec = ignore o Toploop.execute_phrase false Format.std_formatter
  o !Toploop.parse_toplevel_phrase o Lexing.from_string;;

(* exec and a reference idea from miz3.ml yield is_thm, a predicate asking   *)
(* if a string represents a theorem, and exec_thm, which returns the thm.    *)

let thm_ref = ref TRUTH;;

let tactic_ref = ref ALL_TAC;;

let thmlist_tactic_ref = ref REWRITE_TAC;;

let thmtactic_ref = ref MATCH_MP_TAC;;

let is_thm s =
  try exec ("thm_ref := ((" ^ s ^ "): thm);;"); true
  with _ -> false;;

let exec_thm s =
  try if (is_thm s) then !thm_ref else raise Noparse
  with _ -> raise Noparse;;

let exec_tactic s =
  try exec ("tactic_ref := ((" ^ s ^ "): tactic);;"); !tactic_ref
  with _ -> raise Noparse;;

let exec_thmlist_tactic s =
  try
    exec ("thmlist_tactic_ref := ((" ^ s ^ "): thm list -> tactic);;");
    !thmlist_tactic_ref
  with _ -> raise Noparse;;

let exec_thmtactic s =
  try exec ("thmtactic_ref := ((" ^ s ^ "): thm -> tactic);;"); !thmtactic_ref
  with _ -> raise Noparse;;

(* make_env and parse_env_string, following Mizarlight/miz2a.ml and Vince    *)
(* Aravantinos's https://github.com/aravantv/HOL-Light-Q, turn a string to a *)
(* term with types inferred by the goal and assumption list.                 *)

let (make_env: goal -> (string * pretype) list) =
  fun (asl, w) -> map ((fun (s, ty) -> (s, pretype_of_type ty)) o dest_var)
                   (freesl (w::(map (concl o snd) asl)));;

let parse_env_string env s = (term_of_preterm o retypecheck env)
  ((fst o parse_preterm o lex o explode) s);;

(* versions of new_constant, parse_as_infix, new_definition and new_axiom    *)

let NewConstant (x, y) = new_constant(CleanMathFontsForHOL_Light x, y);;

let ParseAsInfix (x, y) = parse_as_infix (CleanMathFontsForHOL_Light x, y);;

let NewDefinition s =
  new_definition (parse_env_string [] (CleanMathFontsForHOL_Light s));;

let NewAxiom s =
  new_axiom (parse_env_string [] (CleanMathFontsForHOL_Light s));;

(* String versions without type annotations of SUBGOAL_THEN, SUBGOAL_TAC,    *)
(* EXISTS_TAC, X_GEN_TAC, EXISTS_TAC and MP_TAC o SPECL.                     *)

let subgoal_THEN stm ttac gl =
  SUBGOAL_THEN (parse_env_string (make_env gl) stm) ttac gl;;

let subgoal_TAC s stm prf gl =
  SUBGOAL_TAC s (parse_env_string (make_env gl) stm) [prf] gl;;

let exists_TAC stm gl =
  EXISTS_TAC (parse_env_string (make_env gl) stm) gl;;

let X_gen_TAC svar (asl, w as gl) =
  let vartype = (snd o dest_var o fst o dest_forall) w in
  X_GEN_TAC (mk_var (svar, vartype)) gl;;

let mp_TAC_specl stermlist sthm gl =
  try
    let termlist = map (fun s -> parse_env_string (make_env gl) s) stermlist in
    (MP_TAC o ISPECL termlist) (exec_thm sthm) gl
  with _ -> raise (Readable_fail ("This is not an mp_TAC_specl expression:
    mp_TAC_specl [" ^ (String.concat "; " stermlist) ^ "]  "^ sthm));;

(* assume transforms a disjunct goal α ∨ β into an implication ¬α ⇒ β and    *)
(* discharges ¬α.  raa allows proofs by contradiction (reductio ad absurdum). *)

let assume lab notalpha tac (asl, w as gl) =
  let t = parse_env_string (make_env gl) notalpha in
  let notalpha_implies_beta = mk_imp(t, mk_conj(t, w)) in
  (SUBGOAL_THEN notalpha_implies_beta (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac] THEN
  HYP REWRITE_TAC lab [MESON[] `!x y. ~x ==> (~x /\ (x \/ y) <=> y)`]) gl;;

let raa lab st tac = subgoal_THEN (st ^ " ==> F") (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac];;

let case_split sDestruct sDisjlist tac =
  let rec list_mk_string_disj = function
      [] -> ""
    | s::[] -> "(" ^ s ^ ")"
    | s::ls -> "(" ^ s ^ ") \\/ " ^ list_mk_string_disj ls in
  subgoal_TAC "" (list_mk_string_disj sDisjlist) tac THEN
  FIRST_X_ASSUM (DESTRUCT_TAC sDestruct);;

(* Basically from the HOL Light tutorial "Towards more readable proofs."     *)

let arithmetic = ARITH_TAC;;
let set_RULE = CONV_TAC SET_RULE;;
let real_RING = CONV_TAC REAL_RING;;
let fol = MESON_TAC;;
let TACtoThmTactic tac = fun  ths -> MAP_EVERY MP_TAC ths THEN tac;;
let NUM_RING_thmTAC = TACtoThmTactic (CONV_TAC NUM_RING);;
let ARITH_thmTAC = TACtoThmTactic ARITH_TAC;;
let REAL_ARITH_thmTAC = TACtoThmTactic REAL_ARITH_TAC;;
let set = TACtoThmTactic set_RULE;;
let so = fun tac -> FIRST_ASSUM MP_TAC THEN tac;;

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
  with Not_found -> raise (Readable_fail ("No final semicolon in " ^ s));;

(* GetProof uses FindMatch to find substrings of the sort                    *)
(* "proof" body "qed;"                                                       *)
(* in a substring s that begins after the "proof", skipping over             *)
(* "proof" ... "qed;" substrings that occur in body.                         *)

let GetProof ByProof s =
  if ByProof = "by" then
    let pos = FindSemicolon s in
    let step, rest = Str.string_before s pos, Str.string_after s (Str.match_end()) in
    (step ^ " ;", rest)
  else
    let pos_after_qed = FindMatch (ws^"proof"^ws) (ws^"qed"^ws0^";") s in
    let pos = Str.search_backward (Str.regexp "qed") s pos_after_qed in
    (Str.string_before s pos, Str.string_after s pos_after_qed);;

(* FindCases uses FindMatch to take a string				     *)
(* "suppose" proof_1 "end;" ... "suppose" proof_n "end;"                     *)
(* and return the list [proof_1; proof_2; ... ; proof_n].                    *)

let rec FindCases s =
  let sleftCase, srightCase = ws^ "suppose" ^ws, ws^ "end" ^ws0^ ";" in
  if Str.string_match (Str.regexp sleftCase) s 0 then
    let CaseEndRest = Str.string_after s (Str.match_end()) in
    let PosAfterEnd = FindMatch sleftCase srightCase CaseEndRest in
    let pos = Str.search_backward (Str.regexp srightCase) CaseEndRest PosAfterEnd in
    let case = Str.string_before CaseEndRest pos
    and rest = Str.string_after CaseEndRest PosAfterEnd in
    case :: (FindCases rest)
  else [];;

(* StringToList uses FindSemicolon to turns a string into the list of        *)
(* substrings delimited by the semicolons which are not captured in lists.   *)

let rec StringToList s =
  if Str.string_match (Str.regexp "[^;]*;") s 0 then
    let pos = FindSemicolon s in
    let head = Str.string_before s pos in
    head :: (StringToList (Str.string_after s (pos + 1)))
  else [s];;

(* StringToTactic uses regexp functions from the Str library to transform a  *)
(* string into a tactic.  The allowable tactics can be written in BNF form   *)
(* as                                                                        *)
(* Tactic := ALL_TAC | Tactic THEN Tactic |                                  *)
(*   one-word-tactic (e.g. ARITH_TAC) |                                      *)
(*   one-word-thm_tactic one-word-thm (e.g. MATCH_MP_TAC num_WF) |           *)
(*   one-word-thmlist_tactic listof(thm | label | - | --) |                  *)
(*   intro_TAC string | exists_TAC string | X_gen_TAC term |                 *)
(*   mp_TAC_specl listof(term) theorem |                                     *)
(*   case_split string listof(statement) Tactic THENL listof(Tactic) |       *)
(*   consider listof(variable) such that statement [label] Tactic |          *)
(*   raa label statement Tactic | assume label statement Tactic |            *)
(*   subgoal_TAC label statement Tactic                                      *)
(*                                                                           *)
(* The allowable string proofs which StringToTactic transforms into tactics  *)
(* can be written in BNF form as                                             *)
(*                                                                           *)
(* OneStepProof := one-word-tactic ";" (e.g. "ARITH_TAC;") |                 *)
(*   one-word-thm_tactic one-word-thm ";" (e.g. "MATCH_MP_TAC num_WF;") |    *)
(*   one-word-thmlist_tactic concatenationof(thm | label | - | --) ";" |     *)
(*   "intro_TAC" string ";" | "exists_TAC" term ";" | "X_gen_TAC" var ";"    *)
(*   "mp_TAC_specl" listof(term) one-word-thm";"                             *)
(*                                                                           *)
(* ByProofQed := "by" OneStepProof | "proof" Proof Proof ...  Proof "qed;"   *)
(*                                                                           *)
(* Proof := "" | OneStepProof | Proof Proof |                                *)
(*   "consider" variable-list "such that" term [label] ByProofQed |          *)
(*   "raa" statement [label] ByProofQed |                                    *)
(*   "assume" statement [label] ByProofQed | statement [label] ByProofQed |  *)
(*   "case_split" destruct ByProofQed                                        *)
(*   "suppose" statement ";" Proof "end;" ...                                *)
(*   "suppose" statement ";" Proof "end;"                                    *)
(*                                                                           *)
(* Case_split reduces the goal to various cases.  In the case_split          *)
(* above, ByProofQed is a proof of the disjunction of the statements, and    *)
(* each Proof solves the goal with its statement added as an assumption.     *)
(* The string destruct lab1 | lab2 | ... has the syntax of DESTRUCT_TAC,     *)
(* so lab1 is the label of the first statement in the first case, etc.       *)
(* The unidentified lower-case words above, e.g. term and statement, are     *)
(* strings.  The label of consider and intro_TAC must also be be nonempty.   *)
(* raa x [l] ByProofQed;                                                     *)
(* is a proof by contradiction (reductio ad absurdum).  ByProofQed proves    *)
(* the goal using the added assumption ~x.  There is a new subgoal F (false) *)
(* which has the added assumption x, also labeled l, which must be nonempty. *)
(* If - is used by ByProofQed, it will refer to ~x, also labeled l.          *)
(* assume x [l] ByProofQed;                                                  *)
(* turns a disjunction goal into a implication with discharged antecedent.   *)
(* ByProofQed is a proof that the goal is equivalent to a disjunction        *)
(* x \/ y, for some statement y.  The label l must nonempty.  Then the goal  *)
(* becomes y, with x an assumption labeled l.                                *)
(* statement [label] ByProofQed;                                             *)
(* is the workhorse of declarative proofs, based on subgoal_TAC: a statement *)
(* with a label and a proof ByProofQed.  Use [] if statement is never used   *)
(* except in the next line, where it can be referred to as - or --.          *)
(* thmlist->tactic ListofLabel-Theorem--;                                    *)
(* is a tactic constructed by a thmlist->tactic, e.g. MESON_TAC (written as  *)
(* fol) followed by a space-separated list of labels, theorems and - or --,  *)
(* which both refer to the previous statement, constructed by HYP.  If --    *)
(* occurs, the previous statement is used by so (using FIRST_ASSUM).  If -   *)
(* occurs, the previous statement is used the way that HYP uses theorems.    *)
(*                                                                           *)
(* Detected errors which result in a failure and an error message:           *)
(* 1) Square braces  [...] must be matched.                                  *)
(* 2) "proof" must be matched  by "qed;", or more precisely,                 *)
(* ws^ "proof" ^ws must be matched  by ";" ^ws^ "qed;",                      *)
(* where ws means nonempty whitespace, except in the  skeleton proof         *)
(* "proof" ws "qed;"                                                         *)
(* 3) In a case_split environment,                                           *)
(* ws^ "suppose" ^ws must be matched by ws^ "end;".                          *)
(* 4) Each step in a proof must end with ";".                                *)
(* 5) A proof must match the BNF for Proof.                                  *)
(* 6) mp_TAC_specl expression must work; e.g. the theorem must be a theorem. *)

let rec StringToTactic s =
  if StringRegexpEqual (Str.regexp ws0) s then ALL_TAC
  else if Str.string_match (Str.regexp (ws^ "case_split" ^ws^ "\([^;]+\)" ^ws^
    "\(by\|proof\)" ^ws)) s 0 then
    let sDestruct = Str.matched_group 1 s
    and (proof, rest) = GetProof (Str.matched_group 2 s)
      (Str.string_after s (Str.group_end 2))
    and SplitAtSemicolon case = Str.bounded_split (Str.regexp ";") case 2 in
    let list2Case = map SplitAtSemicolon (FindCases rest) in
    let listofDisj, listofTac = map hd list2Case, map (hd o tl) list2Case in
    (case_split sDestruct listofDisj (StringToTactic proof))
      THENL (map StringToTactic listofTac)
  else
    let pos = FindSemicolon s in
    let step, rest = Str.string_before s pos, Str.string_after s (Str.match_end()) in
    let (tactic, rest) = StepToTactic s step rest in
      tactic THEN StringToTactic rest
and
StepToTactic s step rest =
  try
    if StringRegexpEqual (Str.regexp (ws0^ "\([^ \t\n]+\)" ^ws0)) step then
      (exec_tactic (Str.matched_group 1 step), rest)
    else raise Not_found
  with _ ->
  try
    if StringRegexpEqual (Str.regexp (ws0^ "\([^][ \t\n]+\)" ^ws0^
      "\([^][ \t\n]+\)" ^ws0)) step then
      ((exec_thmtactic (Str.matched_group 1 step))
      (exec_thm (Str.matched_group 2 step)), rest)
    else raise Not_found
  with _ ->
  try
    if StringRegexpEqual (Str.regexp (ws0^ "\([^ \t\n]+\)\(" ^ws0^
      "[^[]*" ^ws0^ "\)" ^ws0)) step then
      let ttac = exec_thmlist_tactic (Str.matched_group 1 step)
      and LabThmList = Str.split (Str.regexp ws) (Str.matched_group 2 step) in
      let thms = filter is_thm LabThmList
      and labs0 = String.concat " " (filter (not o is_thm) LabThmList) in
      let labs, listofThms = " "^ labs0 ^" ", map exec_thm thms in
      if Str.string_match (Str.regexp ("[^-]*" ^ws^ "-" ^ws)) labs 0 then
        let labs = Str.global_replace (Str.regexp (ws^ "-")) "" labs in
        let tactic = fun (asl, w as gl) ->
          (HYP ttac labs ((snd (hd asl)) :: listofThms)) gl in
        (tactic, rest)
      else if Str.string_match (Str.regexp ("[^-]*" ^ws^ "--" ^ws)) labs 0 then
        let labs = Str.global_replace (Str.regexp (ws^ "--")) "" labs in
        (so (HYP ttac labs listofThms), rest)
      else (HYP ttac labs listofThms, rest)
    else raise Not_found
  with _ ->
  if Str.string_match (Str.regexp (ws0^ "intro_TAC" ^ws)) step 0 then
    let intro_string = (Str.global_replace (Str.regexp ",") ";"
      (Str.string_after step (Str.match_end()))) in
    (INTRO_TAC intro_string, rest)
  else if Str.string_match (Str.regexp (ws0^ "exists_TAC" ^ws)) step 0 then
    let exists_string = Str.string_after step (Str.match_end()) in
    (exists_TAC exists_string, rest)
  else if Str.string_match (Str.regexp (ws0^ "X_gen_TAC" ^ws)) step 0 then
    let gen_string = Str.string_after step (Str.match_end()) in
    (X_gen_TAC gen_string, rest)
  else if
    Str.string_match (Str.regexp (ws0^ "mp_TAC_specl" ^ws^ "\[")) step 0 then
    let ListWsThm = Str.string_after step (Str.match_end()) in
    let RightBrace = FindMatch "\[" "\]" ListWsThm in
    let WsThm = Str.string_after ListWsThm RightBrace
    and tlist = StringToList (Str.string_before ListWsThm (RightBrace - 1)) in
    if StringRegexpEqual (Str.regexp (ws^ "\([^ \t\n]+\)")) WsThm then
      (mp_TAC_specl tlist (Str.matched_group 1 WsThm), rest)
    else raise (Readable_fail (step ^ " is not an mp_TAC_specl expression"))
  else BigStepToTactic s step
and
BigStepToTactic s step =
  if Str.string_match (Str.regexp (ws0^ "consider" ^ws^ "\(\(.\|\n\)+\)" ^ws^
    "such" ^ws^ "that" ^ws^ "\(\(.\|\n\)+\)" ^ws^ "\[\(\(.\|\n\)*\)\]" ^ws^
    "\(by\|proof\)" ^ws)) step 0 then
    let vars, t = Str.matched_group 1 step, Str.matched_group 3 step
    and lab, KeyWord = Str.matched_group 5 step, Str.matched_group 7 step in
    let (proof, rest) = GetProof KeyWord (Str.string_after s (Str.group_end 7))
    and tactic = subgoal_THEN ("?" ^ vars ^ ". " ^ t)
      (DESTRUCT_TAC ("@" ^ vars ^ "." ^ lab)) in
    (tactic THENL [StringToTactic proof; ALL_TAC], rest)
  else
    try
      let start = Str.search_forward (Str.regexp
        (ws^ "\[\([^]]*\)\]" ^ws^ "\(by\|proof\)" ^ws)) step 0 in
      let statement, lab = Str.string_before step start, Str.matched_group 1 step
      and KeyWord = Str.matched_group 2 step
      and AfterWord = Str.string_after s (Str.group_end 2) in
      let (proof, rest) = GetProof KeyWord AfterWord in
      if Str.string_match (Str.regexp (ws0^ "\(raa\|assume\)" ^ws)) statement 0
      then
        let statement = Str.string_after statement (Str.match_end()) in
        if Str.matched_group 1 step = "raa" then
          (raa lab statement (StringToTactic proof), rest)
        else (assume lab statement (StringToTactic proof), rest)
      else (subgoal_TAC lab statement (StringToTactic proof), rest)
    with Not_found -> raise (Readable_fail ("can't parse "^ step));;

let theorem s =
  let s = CleanMathFontsForHOL_Light s in
  try
    let start = Str.search_forward (Str.regexp
      (ws ^ "proof" ^ws^ "\(\(.\|\n\)*\)" ^ws ^ "qed" ^ws0^ ";" ^ws0)) s 0 in
    let thm, proof = Str.string_before s start, Str.matched_group 1 s in
    prove (parse_env_string [] thm, StringToTactic proof)
  with Not_found -> raise (Readable_fail
    ("Missing initial \"proof\" or final \"qed;\" in\n" ^ s));;

let interactive_proof s =
  let proof = CleanMathFontsForHOL_Light s in
  e (StringToTactic proof);;

let interactive_goal s =
  let thm = CleanMathFontsForHOL_Light s in
  g (parse_env_string [] thm);;

(* The uncluttered interface is shown by a proof from the HOL Light tutorial *)
(* section 14.1 "Choice and the select operator" and a proof from arith.ml.  *)

let AXIOM_OF_CHOICE = theorem `;
  ∀P. (∀x. ∃y. P x y) ⇒ ∃f. ∀x. P x (f x)

  proof
    intro_TAC ∀P, H1;
    exists_TAC λx. @y. P x y;
    fol H1;
  qed;
`;;

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    mp_TAC_specl [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

let NSQRT_2 = theorem `;
  ∀p q. p * p = 2 * q * q  ⇒  q = 0

  proof
    MATCH_MP_TAC num_WF;
    intro_TAC ∀p, A, ∀q, B;
    EVEN(p * p) ⇔ EVEN(2 * q * q)     [] by fol B;
    EVEN(p)     [] by fol - ARITH EVEN_MULT;
    consider m such that p = 2 * m     [C] by fol - EVEN_EXISTS;
    case_split qp | pq by arithmetic;
    suppose q < p;
      q * q = 2 * m * m ⇒ m = 0     [] by fol qp A;
      NUM_RING_thmTAC - B C;
    end;
    suppose      p <= q;
      p * p <= q * q     [] by fol - LE_MULT2;
      q * q = 0     [] by ARITH_thmTAC - B;
    NUM_RING_thmTAC -;
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
    EVEN(p)     [] by fol - ARITH EVEN_MULT;
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
      NUM_RING_thmTAC - B C;
`;;
interactive_proof `;
      p * p <= q * q     [] by fol - LE_MULT2;
      q * q = 0     [] by ARITH_thmTAC - B;
      NUM_RING_thmTAC -;
`;;
let NSQRT_2 = top_thm();;
