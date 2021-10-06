(*
        Author: Thomas C. Hales, 2003

        GCD_CONV takes two HOL-light terms (NUMERALs) a and b and
        produces a theorem of the form
                |- GCD a b = g

        (In particular, the arguments cannot be negative.)

*)


prioritize_num();;

let DIVIDE = new_definition(`DIVIDE a b = ?m. (b = m*a )`);;

parse_as_infix("||",(16,"right"));;

override_interface("||",`DIVIDE:num->num->bool`);;

(* Now prove the lemmas *)

let DIV_TAC t =   EVERY[ REP_GEN_TAC;
   REWRITE_TAC[DIVIDE];
   DISCH_ALL_TAC;
   REPEAT (FIRST_X_ASSUM CHOOSE_TAC);
   TRY (EXISTS_TAC t)];;


let DIVIDE_DIVIDE = prove_by_refinement(
  `!a b c. (((a || b) /\ (b || c)) ==> (a || c))`,
   [
   DIV_TAC `m'*m`;
   ASM_REWRITE_TAC[MULT_ASSOC]
   ]);;

let DIVIDE_EQ = prove_by_refinement(
   `! a b. (((a || b) /\ (b || a)) ==> (a = b))`,
  [
  DIV_TAC `1`;
  FIRST_X_ASSUM (fun th -> (POP_ASSUM MP_TAC) THEN REWRITE_TAC[th]);
  ASM_CASES_TAC `b=0`;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  REWRITE_TAC[ARITH_RULE `(b = m*m'*b) = (1*b = m*m'*b)`];
  ASM_REWRITE_TAC[MULT_ASSOC;EQ_MULT_RCANCEL];
  DISCH_THEN (fun th -> MP_TAC (REWRITE_RULE[MULT_EQ_1] (GSYM th)) );
  DISCH_THEN (fun th -> REWRITE_TAC[CONJUNCT2 th] THEN ARITH_TAC);
  ]);;

let DIVIDE_SUM = prove_by_refinement(
  `!a b h. (((h || a) /\ (h||b)) ==> (h || (a+b)))`,
  [
  DIV_TAC `m+m'`;
  ASM_REWRITE_TAC[ARITH;RIGHT_ADD_DISTRIB];
  ]);;

let DIVIDE_SUMMAND = prove_by_refinement(
  `!a b h. (((h|| b) /\ (h || (a+b))) ==> (h|| a))`,
   [
   DIV_TAC `m'-m`;
   REWRITE_TAC[RIGHT_SUB_DISTRIB];
   REPEAT (FIRST_X_ASSUM  (fun th -> REWRITE_TAC[GSYM th]));
   ARITH_TAC;
   ]);;

let DIVIDE_PROD = prove_by_refinement(
   `!a b h. (((h|| a) ==> (h || (b*a))))`,
   [
   DIV_TAC `b*m`;
   ASM_REWRITE_TAC[MULT_ASSOC];
   ]);;

let DIVIDE_PROD2 = prove_by_refinement(
   `!a b h. (((h|| a) ==> (h || (a*b))))`,
   [
   DIV_TAC `b*m`;
   ASM_REWRITE_TAC[MULT_AC]
   ]);;

let GCD = new_definition(`GCD a b = @g.
        ((g || a) /\ (g || b) /\
        (!h. (((h || a) /\ (h || b)) ==> (h || g))))`);;

let gcd_certificate = prove(`!a b g. ((? r s r' s' a' b'.
        ((a = a'*g) /\ (b = b'*g) /\ (g +r'*a+s'*b= r*a + s*b)))
        ==> (GCD a b = g))`,
        let tac1 = (
        (REPEAT GEN_TAC)
        THEN (DISCH_TAC)
        THEN (REPEAT (POP_ASSUM CHOOSE_TAC))
        THEN (REWRITE_TAC[GCD])
        THEN (MATCH_MP_TAC SELECT_UNIQUE)
        THEN BETA_TAC
        THEN GEN_TAC
        THEN EQ_TAC) and

        ygbranch = (
        DISCH_TAC
        THEN (MATCH_MP_TAC DIVIDE_EQ)
        THEN CONJ_TAC) and

        ydivg_branch = (
        (SUBGOAL_TAC (` (y || (r*a + s*b))/\ (y || (r'*a +s'*b))`))
        THENL [((ASM MESON_TAC)[DIVIDE_SUM;DIVIDE_PROD]);
        ((ASM MESON_TAC)[DIVIDE_SUMMAND])]
        ) and

        gdivy_branch = (
        (UNDISCH_TAC
          (`(y||a) /\ (y ||b) /\ (!h. (((h||a)/\(h||b))==> (h||y)))`))
        THEN (TAUT_TAC (` (A ==> B) ==> ((C /\ D/\ A)==> B)`))
        THEN (DISCH_TAC)
        THEN (POP_ASSUM MATCH_MP_TAC)
        THEN (REWRITE_TAC[DIVIDE])
        THEN (CONJ_TAC)
        THEN ((ASM MESON_TAC)[])
                ) and

        yghyp_branch = (
        (DISCH_TAC)
        THEN (let x t = REWRITE_TAC[t] in (POP_ASSUM x))
        THEN (CONJ_TAC)
        THENL [((ASM MESON_TAC)[DIVIDE]);ALL_TAC]
        THEN (CONJ_TAC)
        THENL [((ASM MESON_TAC)[DIVIDE]);ALL_TAC]
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN (SUBGOAL_TAC (` (h || (r*a + s*b))/\ (h || (r'*a+s'*b))`))
        THENL [((ASM MESON_TAC)[DIVIDE_SUM;DIVIDE_PROD]);
                ((ASM MESON_TAC)[DIVIDE_SUMMAND])]
                ) in
        tac1 THENL [ygbranch THENL [ydivg_branch;gdivy_branch];yghyp_branch]);;

(* Now compute gcd with CAML num calculations,
   then check the answer in HOL-light *)
let gcd_num x1 x2 =
        let rec gcd_data (a1,b1,x1,a2,b2,x2) =
        if (x1 < (Int 0)) then
                gcd_data(minus_num a1,minus_num b1,minus_num x1,a2,b2,x2)
        else if (x2 < (Int 0)) then gcd_data(a1,b1,x1,minus_num a2,minus_num
        b2,minus_num x2)
        else if (x1 = (Int 0)) then (a2,b2,x2)
        else if (x1>x2) then gcd_data (a2,b2,x2,a1,b1,x1)
        else (
                let r = (quo_num x2 x1) in
                gcd_data (a1,b1,x1,a2 -/ r*/ a1,b2 -/ r*/ b1, x2 -/ r*/ x1)
             ) in
        gcd_data ((Int 1),(Int 0),x1,(Int 0),(Int 1),x2);;

let gcd_num x1 x2 =
        let rec gcd_data (a1,b1,x1,a2,b2,x2) =
        if (x1 < (Int 0)) then
                gcd_data(minus_num a1,minus_num b1,minus_num x1,a2,b2,x2)
        else if (x2 < (Int 0)) then gcd_data(a1,b1,x1,minus_num a2,minus_num
        b2,minus_num x2)
        else if (x1 = (Int 0)) then (a2,b2,x2)
        else if (x1>x2) then gcd_data (a2,b2,x2,a1,b1,x1)
        else (
                let r = (quo_num x2 x1) in
                gcd_data (a1,b1,x1,a2 -/ r*/ a1,b2 -/ r*/ b1, x2 -/ r*/ x1)
             ) in
        gcd_data ((Int 1),(Int 0),x1,(Int 0),(Int 1),x2);;

        (* g = gcd, (a',b') = (a,b)/g, g +r1'*a+s1'*b = r1*a+s1*b *)
let gcd_numdata a b =
        let a = abs_num a in
        let b = abs_num b in
        let Z = Int 0 in
        let (r,s,g) = gcd_num a b in
        let a' = if (g=Z) then Z else round_num(a//g) in
        let b' = if (g=Z) then Z else round_num(b//g) in
        let _ = if not(a=a'*/g) then failwith "GCD_CONV a" else 0 in
        let _ = if not(b=b'*/g) then failwith "GCD_CONV b" else 0 in
        let _ = if not(g=r*/a+/s*/b) then failwith "GCD_CONV g" else 0 in
        let (r1,r1') = if (r >/ Z) then (r,Z) else (Z,minus_num r) in
        let (s1,s1') = if (s >/ Z) then (s,Z) else (Z,minus_num s) in
        (g,a,b,a',b',r1',s1',r1,s1);;

(* Here is the conversion.
        Example:
                GCD_CONV (`66`) (`144`)

*)
let GCD_CONV at bt =
        let a = dest_numeral at in
        let b = dest_numeral bt in
        let (g,a,b,a',b',r1',s1',r1,s1) = gcd_numdata a b in
        prove(parse_term("GCD "^(string_of_num a)^" "^(string_of_num b)^" = "^
                (string_of_num g)),
                (MATCH_MP_TAC gcd_certificate)
                THEN (EXISTS_TAC (mk_numeral r1))
                THEN (EXISTS_TAC (mk_numeral s1))
                THEN (EXISTS_TAC (mk_numeral r1'))
                THEN (EXISTS_TAC (mk_numeral s1'))
                THEN (EXISTS_TAC (mk_numeral a'))
                THEN (EXISTS_TAC (mk_numeral b'))
                THEN (ARITH_TAC));;

(* Example:
        hol_gcd 66 144

   This version can overflow on CAML integers before it reaches hol-light.
   Example:
        hol_gcd 1000000000000000000 10000000000000000000000
        - : thm = |- GCD 660865024 843055104 = 262144
*)

let hol_gcd a b = GCD_CONV (mk_small_numeral a) (mk_small_numeral b);;

remove_interface ("||");;
pop_priority();;


(* test code *)

exception Test_suite_num_ext_gcd of string;;

(* For the tests we use integers a and b.  These can overflow if
   a and b are too large, so that we should confine ourselves to
   tests that are not too large.
*)

let test_num_ext_gcd (a, b) =
  let a1 = string_of_int (abs a) in
  let b1 = string_of_int (abs b) in
  let c = gcd a b in
  let c1 = string_of_int (abs c) in
  let th = GCD_CONV (mk_small_numeral a) (mk_small_numeral b) in
  if (not (hyp th = ([]:term list))) then raise
    (failwith ("num_ext_gcd test suite failure "^a1^" "^b1))
  else if (not (concl th = (parse_term ("GCD "^a1^" "^b1^"="^c1))))
    then raise (failwith ("num_ext_gcd test suite failure "^a1^" "^b1))
  else ();;


let test_suite_num_ext_gcd  =
  let _ =
    map test_num_ext_gcd
      [(0,0);(0,1);(1,0);(-0,-0);
       (2,3);(4,6);
       (0,2);(2,0);
       (10,100);(100,10);(17,100);(100,17)] in
   print_string "num_ext_gcd loaded\n";;

let divide = DIVIDE and
    gcd = GCD and
    gcd_conv = GCD_CONV;;

