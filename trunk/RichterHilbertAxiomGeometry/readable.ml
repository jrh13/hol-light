(* ========================================================================= *)
(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(* Miz3 interface for tactics proof, so the syntax before the keyword "by"   *)
(* emulates miz3.ml, with the aim of improved readability of formal proofs,  *)
(* with few type annotations, doublequotes, backquotes and semicolons in     *)
(* lists.  Uses a version of INTRO_TAC, consider, case_split.  Statements    *)
(* to be proved are merely written, with the SUBGOAL_TAC hidden.  Semicolons *)
(* are used essentially as THEN connecting tactics.  THENL is currently      *)
(* only allowed implicitly in case_split.  More general tactics proofs could *)
(* be allowed than are presently, but allowing completely arbitrary proofs   *)
(* will impede readability, so there's a tradeoff.  An interactive mode is   *)
(* useful in debugging proofs.  An advantage over miz3 is that REWRITE_TAC   *)
(* and SIMP_TAC can be used intelligently, as we have structured proofs, and *)
(* not an  unordered commma separated "by" list.  Miz3 proofs are primarily  *)
(* done by MESON_TAC.  Another advantage is that the semantics is obvious,   *)
(* as there is a straightforward translation to HOL Light tactics proofs.    *)
(* Many math characters (∃, ⇒ etc) are allowed as in HOL4 and Isabelle.     *)

#load "str.cma";;

(* parse_qproof uses system.ml quotexpander feature designed for miz3.ml to  *)
(* turn backquoted expression `;[...]` into a string with no newline or      *)
(* backslash problems.  This miz3 emulation can not be used simultaneously   *)
(* with miz3, which defines parse_qproof differently.                        *)

let parse_qproof s = (String.sub s 1 (String.length s - 1));;

(* exec_thm, taken from miz3.ml, maps a string to its theorem, and defines   *)
(* the predicate is_thm which tests if a string represents a theorem.        *)

let exec_phrase b s =
  let lexbuf = Lexing.from_string s in
  let ok = Toploop.execute_phrase b Format.std_formatter
    (!Toploop.parse_toplevel_phrase lexbuf) in
  Format.pp_print_flush Format.std_formatter ();
  (ok,
   let i = lexbuf.Lexing.lex_curr_pos in
   String.sub lexbuf.Lexing.lex_buffer
     i (lexbuf.Lexing.lex_buffer_len - i));;

let exec_thm_out = ref TRUTH;;

let exec_thm s =
  try
    let ok,rst = exec_phrase false
      ("exec_thm_out := (("^s^") : thm);;") in
    if not ok or rst <> "" then raise Noparse;
    !exec_thm_out
  with _ -> raise Noparse;;

let exec_thmlist_tactic_out = ref REWRITE_TAC;;

let exec_thmlist_tactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_thmlist_tactic_out := (("^s^") : thm list -> tactic);;") in
    if not ok or rst <> "" then raise Noparse;
    !exec_thmlist_tactic_out
  with _ -> raise Noparse;;

let exec_thmtactic_out = ref MATCH_MP_TAC;;

let exec_thmtactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_thmtactic_out := (("^s^") : thm -> tactic);;") in
    if not ok or rst <> "" then raise Noparse;
    !exec_thmtactic_out
  with _ -> raise Noparse;;

let exec_tactic_out = ref ALL_TAC;;

let exec_tactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_tactic_out := (("^s^") : tactic);;") in
    if not ok or rst <> "" then raise Noparse;
    !exec_tactic_out
  with _ -> raise Noparse;;

let is_thm s =
  try let thm = exec_thm s in true
  with _ -> false;;

let is_tactic s =
  try let tactic = exec_tactic s in true
  with _ -> false;;

let is_thmtactic s =
  try let ttac = exec_thmtactic s in true
  with _ -> false;;

let is_thmlist_tactic s =
  try let thmlist_tactic = exec_thmlist_tactic s in true
  with _ -> false;;

(* make_env and parse_env_string, following Mizarlight/miz2a.ml and Vince    *)
(* Aravantinos's https://github.com/aravantv/HOL-Light-Q, turn a string to a *)
(* term with types inferred by the goal and assumption list. The versions    *)
(* of SUBGOAL_THEN, SUBGOAL_TAC, EXISTS_TAC, X_GEN_TAC, case_split and       *)
(* consider can be used generally, especially with _split and consider use   *)
(* DESTRUCT_TAC, so the labels sDestruct and lab must be nonempty strings; a *)
(* warning holds for case_split and consider in our miz3 emulation.          *)

let (make_env: goal -> (string * pretype) list) =
  fun (asl,w) -> map ((fun (s,ty) -> s,pretype_of_type ty) o dest_var)
                   (freesl (w::(map (concl o snd) asl)));;

let parse_env_string env s = (term_of_preterm o retypecheck env)
  ((fst o parse_preterm o lex o explode) s);;

let (subgoal_THEN: string -> thm_tactic -> tactic) =
  fun stm ttac gl -> 
    let t = parse_env_string (make_env gl) stm in
    SUBGOAL_THEN t ttac gl;;

let subgoal_TAC s stm prfs gl =
  let t = parse_env_string (make_env gl) stm in
  SUBGOAL_TAC s t prfs gl;;

let (exists_TAC: string -> tactic) =
  fun stm gl -> let env = make_env gl in
    EXISTS_TAC (parse_env_string env stm) gl;;

let (X_gen_TAC: string -> tactic) =
  fun svar (asl,w as gl) ->
    let vartype = (snd o dest_var o fst o dest_forall) w in
    X_GEN_TAC (mk_var (svar,vartype)) gl;;

let assume lab notalpha tac (asl,w as gl) = 
  let t = parse_env_string (make_env gl) notalpha in
  let notalpha_implies_beta = mk_imp(t, mk_conj(t, w)) in 
  (SUBGOAL_THEN notalpha_implies_beta (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac] THEN 
  HYP REWRITE_TAC lab [MESON[] `!x y. ~x ==> (~x /\ (x \/ y) <=> y)`]) gl;;

let case_split sDestruct sDisjlist tac =
  let rec list_mk_string_disj = function
      [] -> ""
    | s::[] -> "(" ^ s ^ ")"
    | s::ls -> "(" ^ s ^ ") \\/ " ^ list_mk_string_disj ls in
  subgoal_TAC "" (list_mk_string_disj sDisjlist) tac THEN
  FIRST_X_ASSUM (DESTRUCT_TAC sDestruct);;

let consider vars_t prfs lab =
  let noSuchThat = Str.bounded_split (Str.regexp
    "[ \t\n]+such[ \t\n]+that[ \t\n]+") vars_t 2 in
  let vars = hd noSuchThat and
  t = hd (tl noSuchThat) in
  match prfs with
    p::ps -> (warn (ps <> []) "consider: additional subproofs ignored";
    subgoal_THEN ("?" ^ vars ^ ". " ^ t)
    (DESTRUCT_TAC ("@" ^ vars ^ "." ^ lab)) THENL [p; ALL_TAC])
  | [] -> failwith "consider: no subproof given";;

let raa lab st tac = subgoal_THEN (st ^ " ==> F") (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac];;

let raa lab st tac = fun gl -> 
  let t = parse_env_string (make_env gl) st in
  (SUBGOAL_THEN (mk_imp(t,`F`)) (LABEL_TAC lab) THENL [INTRO_TAC lab; tac]) gl;;

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

(* Allows HOL4 and Isabelle style math characters, via parse_qproof.         *)

let CleanMathFontsForHOL_Light s =
  let rec clean s loStringPairs =
    match loStringPairs with
      [] -> s
    | (hd :: tl) ->
      let symbol = fst hd and ascii = snd hd in
        let s = Str.global_replace (Str.regexp symbol) ascii s in
        clean s tl in
  clean s ["⇒","==>"; "⇔","<=>"; "∧","/\\ "; "∨","\\/"; "¬","~";
    "∀","!"; "∃","?"; "∈","IN"; "∉","NOTIN";
    "α","alpha"; "β","beta"; "γ","gamma"; "λ","\\ "; "θ","theta"; "μ","mu";
    "⊂","SUBSET"; "∩","INTER"; "∪","UNION"; "∅","{}"; "━","DELETE";
    "≡", "==="; "≅", "cong"; "∡", "angle"; "∥","parallel"];;

let ws = "[ \t\n]+";;
let ws0 = "[ \t\n]*";;

let StringRegexpEqual r s = Str.string_match r s 0 &&
  s = Str.matched_string s;;

(* StringToTacticsProof uses regexp functions from the Str library to turn   *)
(* string into a tactics proof.  Most of the work is in ConvertToHOL, which  *)
(* matches and converts strings of the following sort.                       *)
(* 1) a one-word tactic, e.g. ARITH_TAC.                                     *)
(* 2) a one-word thm_tactic and a thm, e.g. MATCH_MP_TAC num_WF.             *)
(* 3) intro_TAC followed by a nonempty comma-separated intro string.         *)
(* 4) exists_TAC term; the term a string with few type annotations.          *)
(* 5) consider vars such that t  [label] by tactic;                          *)
(* label must be nonempty, as consider uses DESTRUCT_TAC.                    *)
(* 6) raa x [l] by p;                                                        *)
(* a proof by contradiction ("reductio ad absurdum").  The tactic p proves   *)
(* the goal using the added assumption ~x.  There is a new subgoal false     *)
(* which has the added assumption x, also labeled l, which must be nonempty. *)
(*  Note that if - is used by p, it will refer to ~x, also labeled l.        *)
(* 7) assume x [l] by p;                                                     *)
(* The tactic p is a proof that the goal is a disjunction x \/ y.  Then the  *)
(* goal becomes y, with x an assumption labeled l, which must be nonempty.   *)
(* 8) statement [label] by tactic;  Unlike miz3, there must be a label, so   *)
(* use the empty label [] if this statement will never be referred to except *)
(* in the next line, where it can be referred to as -.                       *)
(* 9) thmlist->tactic labels [theorems], often a proof of a statement or     *)
(* consider expression, although it can be a entire line.  The lists labels  *)
(* and theorems are space- and comma-separated resp. The tactic obtained is  *)
(* HYP thmlist->tactic "labels" [theorems] unless - occurs in labels, and    *)
(* then so (using FIRST_ASSUM) references the previous statement.            *)
(* The tactics proofs here can be built using THEN.                          *)

let rec ByProof s = 
  let l = Str.split (Str.regexp (ws^ "THEN" ^ws)) s in 
  end_itlist (fun x y -> x THEN y) (map ConvertToHOL l)
and
ConvertToHOL s = 
  if StringRegexpEqual (Str.regexp (ws0^ "\([^ \t\n]+\)" ^ws0)) s &&
    is_tactic (Str.matched_group 1 s)
  then
    exec_tactic (Str.matched_group 1 s)
  else
  if StringRegexpEqual (Str.regexp
    (ws0^ "\([^][ \t\n]+\)" ^ws0^ "\([^][ \t\n]+\)" ^ws0)) s &&
    is_thmtactic (Str.matched_group 1 s) &&
    is_thm (Str.matched_group 2 s)
  then
    let ttac = (Str.matched_group 1 s) and
    thm = (Str.matched_group 2 s) in
    (exec_thmtactic ttac) (exec_thm thm)
  else
  if Str.string_match (Str.regexp (ws0^ "intro_TAC" ^ws)) s 0
  then
    let intro_string = (Str.global_replace (Str.regexp ",") ";"
      (Str.string_after s (String.length (Str.matched_string s)))) in
      INTRO_TAC intro_string
  else
  if Str.string_match (Str.regexp (ws0^ "exists_TAC" ^ws)) s 0
  then
    exists_TAC (Str.string_after s (String.length (Str.matched_string s)))
  else
  if Str.string_match (Str.regexp (ws0^ "X_gen_TAC" ^ws)) s 0
  then
    X_gen_TAC (Str.string_after s (String.length (Str.matched_string s)))
  else
  if Str.string_match (Str.regexp (ws0^ "consider" ^ws^ "\(\(.\|\n\)+\)"
    ^ws^"such" ^ws^ "that" ^ws^ "\(\(.\|\n\)+\)" ^ws^ "\[\(\(.\|\n\)*\)\]"
    ^ws^ "by" ^ws)) s 0
  then
    let vars = Str.matched_group 1 s and
    t = Str.matched_group 3 s and
    lab = Str.matched_group 5 s and
    tac = Str.string_after s (String.length (Str.matched_string s)) in
    subgoal_THEN ("?" ^ vars ^ ". " ^ t)
    (DESTRUCT_TAC ("@" ^ vars ^ "." ^ lab)) THENL [ByProof tac; ALL_TAC]
 else
  if Str.string_match (Str.regexp (ws0^ "raa" ^ "\(\(.\|\n\)+\)" ^ws^
    "\[\([^]]*\)\]" ^ws^ "by" ^ws)) s 0
  then
    let statement = Str.matched_group 1 s and
    lab = Str.matched_group 3 s and
    tac = (Str.string_after s (String.length (Str.matched_string s))) in
    raa lab statement (ByProof tac)
  else 
  if Str.string_match (Str.regexp (ws0^ "assume" ^ "\(\(.\|\n\)+\)" ^ws^ 
    "\[\([^]]*\)\]" ^ws^ "by" ^ws)) s 0
  then
    let statement = Str.matched_group 1 s and
    lab = Str.matched_group 3 s and
    tac = (Str.string_after s (String.length (Str.matched_string s))) in
    assume lab statement (ByProof tac)
  else 
  try 
    let start = Str.search_forward (Str.regexp 
    (ws^ "\[\([^]]*\)\]" ^ws^ "by" ^ws)) s 0 in
    let statement = Str.string_before s start and
    lab = Str.matched_group 1 s and
    tac = Str.string_after s (Str.match_end()) in
    subgoal_TAC lab statement [ByProof tac]
  with Not_found ->
  if StringRegexpEqual (Str.regexp (ws0^ "\([^ \t\n]+\)\(" ^ws0^ "[^[]*"
    ^ws0^ "\)" ^ws0)) s &&
    is_thmlist_tactic (Str.matched_group 1 s)
  then
    try
      let ttac = exec_thmlist_tactic (Str.matched_group 1 s) and
      LabThmList = Str.split (Str.regexp ws) (Str.matched_group 2 s) in
      let thms = filter is_thm LabThmList and 
      labs0 = String.concat " " (filter (not o is_thm) LabThmList) in
      let labs = " "^ labs0 ^" " and 
      listofThms = map exec_thm thms in
      if Str.string_match (Str.regexp ("[^-]*" ^ws^ "-" ^ws)) labs 0
      then
        let labs_minus = Str.global_replace (Str.regexp (ws^ "-")) "" labs in
        fun (asl,w as gl) -> 
          (HYP ttac labs_minus ((snd (hd asl)) :: listofThms)) gl
      else if Str.string_match (Str.regexp ("[^-]*" ^ws^ "--" ^ws)) labs 0
      then
        let labs_minus = Str.global_replace (Str.regexp (ws^ "--")) "" labs in
        so (HYP ttac labs_minus listofThms)
      else HYP ttac labs listofThms
    with  _ -> warn (true) "square-brace following thm_list->tactic is not a comma-separated list of theorems"; ALL_TAC
  else ALL_TAC;;

let rec FindMatch sleft sright s =
  let test = Str.regexp ("\("^ sleft ^"\|"^ sright ^"\)") and
  left = (Str.regexp sleft) in  
  let rec FindMatchPosition s count = 
    if count = 1 then 0 else 
      try 
        let start = Str.search_forward test s 0 in
        let endpos = Str.match_end() in 
        let rest = Str.string_after s endpos and
        increment = 
          if StringRegexpEqual left (Str.matched_group 1 s) then -1 else 1 in
        endpos + (FindMatchPosition rest (count + increment))
      with Not_found -> warn (true) "no matching right bracket operator to left bracket operator";
        -1 in 
  FindMatchPosition s 0;;

(* StringToTacticsProof handles case_split and long proofs of statements,    *)
(* two matters that involve semicolons, and leaves the remaining work to     *)
(* ConvertToHOL.  A long proof of statement has the form                     *)
(* statement [lab] "proof" body_1; body_2; ...; body_n; "qed";               *)
(* A case_split which has the form                                           *)
(* "case_split" sDestruct "by" tactic;                                       *)
(* "suppose" dj1;                                                            *)
(*   <proof1>                                                                *)
(*   "end";                                                                  *)
(* "suppose" dj2;                                                            *)
(*   <proof2>                                                                *)
(*   "end";                                                                  *)
(* "suppose" dj2;                                                            *)
(*   <proof2>                                                                *)
(*   "end";                                                                  *)
(* ...                                                                       *)
(* where tactic is a proof of the disjunction dj1 \/ dj2 \/ ..., and proof1  *)
(* is a proof of the goal with the added assumptions dj1, etc. sDestruct is  *)
(* a nonempty string of the sort lab1 | lab2 | ... required by DESTRUCT_TAC. *)

let rec StringToTactic s =
  let sleftCase = ws^ "suppose" ^ws and
  srightCase = ws^ "end" ^ws0^ ";" and
  sleftProof = ws^ "proof" ^ws and
  srightProof = ";" ^ws^ "qed" ^ws0^ ";" in

let rec FindCases s =
  if Str.string_match (Str.regexp sleftCase) s 0
  then 
    let case_end_rest = Str.string_after s (Str.match_end()) in 
    let pos_after_end = FindMatch sleftCase srightCase case_end_rest in 
    let pos = Str.search_backward (Str.regexp srightCase) 
      case_end_rest pos_after_end in
    let case = Str.string_before case_end_rest pos and
    rest = " "^ (Str.string_after case_end_rest pos_after_end) in 
      (case ^" ") :: (FindCases rest)
  else [] in 

  let test = Str.regexp ("\("^ sleftProof ^"\|"^ "case_split" ^ws^"\)") and
  rleft = Str.regexp (sleftProof) in 
  try
    let start = Str.search_forward test s 0 in 
    if StringRegexpEqual rleft (Str.matched_group 1 s) 
    then 

      let start = Str.search_forward (Str.regexp 
	(ws^ "\[\([^]]*\)\]" ^ sleftProof)) s 0 in
      let before_statement = (Str.string_before s start) and
      lab = Str.matched_group 1 s and
      body_qed_rest = Str.string_after s (Str.match_end()) in
      let pos_after_qed = FindMatch sleftProof srightProof body_qed_rest in 
      let pos = Str.search_backward (Str.regexp srightProof) 
	body_qed_rest pos_after_qed in
      let body = (Str.string_before body_qed_rest pos) ^ "; " and
      rest = " "^ (Str.string_after body_qed_rest pos_after_qed) in 
      let before,statement = 
      try 
	let start = Str.search_backward (Str.regexp ";") 
	  before_statement (String.length before_statement) in 
	Str.string_before before_statement start,
	Str.string_after before_statement (Str.match_end())
      with Not_found -> 
      "", before_statement in
      (StringToTactic before) THEN
      (subgoal_TAC lab statement [StringToTactic body]) THEN
      (StringToTactic rest)

    else 
      let start = Str.search_forward (Str.regexp ("case_split" ^ws^
	"\([^;]+\)" ^ ws^ "by" ^ws^ "\([^;]+\)" ^ ";" ^ws)) s 0 in
      let before = Str.string_before s start and 
      sDestruct = (Str.matched_group  1 s) and 
      tac = (Str.matched_group 2 s) and
      rest = Str.string_after s (Str.match_end()) in
      let loCase = FindCases (" "^ rest ^" ") in
	let suppose_proof case =
	  let start = Str.search_forward (Str.regexp ";") case 0 in
	  (Str.string_before case start, Str.string_after case
	  (Str.match_end())) in
	let pairCase = map suppose_proof loCase in
	let listofDisj = map fst pairCase and
	listofTac = map snd pairCase in
	StringToTactic before THEN
	  (case_split sDestruct listofDisj [ConvertToHOL tac])
	  THENL (map StringToTactic listofTac)

  with Not_found -> 
  let l = Str.split (Str.regexp (ws0^ ";" ^ws)) s in
  if l = [] then ALL_TAC else 
  end_itlist (fun x y -> x THEN y) (map (ConvertToHOL o 
    (fun s -> Str.global_replace (Str.regexp "!!!") ";" s)) l);;

let rec StringToTacticsProof s =
  let rec HideListSemicolons s =
    try 
      let start = Str.search_forward (Str.regexp "\[") s 0 in
      let beginning = Str.string_before s (start + 1) and
      region_rest = Str.string_after s (Str.match_end()) in
      let MatchingSquareBrace = FindMatch "\[" "\]" region_rest in
      let region = Str.string_before region_rest MatchingSquareBrace and
      rest =  Str.string_after region_rest MatchingSquareBrace in
      let HiddenRegion = Str.global_replace (Str.regexp ";") " !!! " region in
      beginning ^ HiddenRegion ^ (HideListSemicolons rest)
    with Not_found -> s in 
  StringToTactic (HideListSemicolons s);;

let theorem s =
  let s = CleanMathFontsForHOL_Light s in
  let start = Str.search_forward (Str.regexp 
    (ws ^ "proof" ^ws^ "\(\(.\|\n\)+;\)" ^ws ^ "qed" ^ws0^ ";" ^ws0)) s 0 in
  let thm = Str.string_before s start and
  proof = (Str.matched_group 1 s) ^" " in
  prove (parse_env_string [] thm,   StringToTacticsProof proof);;

let interactive_proof s =
  let proof = CleanMathFontsForHOL_Light s in
  e (StringToTacticsProof proof);;

let interactive_goal s =
  let thm = CleanMathFontsForHOL_Light s in
  g (parse_env_string [] thm);;


needs "Examples/holby.ml";;

let hol_by = CONV_TAC o HOL_BY;;

let AXIOM_OF_CHOICE = theorem `;
  ∀P. (∀x. ∃y. P x y) ==> ∃f. ∀x. P x (f x)

  proof
    intro_TAC ∀P, H1;
    exists_TAC \x. @y. P x y;
    fol H1;
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

interactive_goal `;∀p q. p * p = 2 * q * q  ⇒  q = 0
`;;
interactive_proof `;
    MATCH_MP_TAC num_WF;
    intro_TAC ∀p, A, ∀q, B;
    EVEN(p * p) ⇔ EVEN(2 * q * q)     [] proof fol B; qed;
    EVEN(p)     [] by fol - ARITH EVEN_MULT;
    consider m such that p = 2 * m     [C] by fol - EVEN_EXISTS;
`;;
interactive_proof `;
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
`;;

(*

interactive_goal `;
`;;
interactive_proof `;
`;;
interactive_proof `;
`;;
interactive_proof `;
`;;
interactive_proof `;
`;;
interactive_proof `;
`;;
interactive_proof `;
`;;
interactive_proof `;
`;;
interactive_proof `;
`;;

*)
        
