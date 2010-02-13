(* ========================================================================= *)
(* Church-Rosser property for combinatory logic (S and K combinators).       *)
(*                                                                           *)
(* This is adapted from a HOL4 develoment, itself derived from an old HOL88  *)
(* example by Tom Melham and Juanito Camilleri. For a detailed discussion,   *)
(* see pp. 29-39 of the following paper:                                     *)
(*                                                                           *)
(*    http://www.comlab.ox.ac.uk/tom.melham/pub/Camilleri-1992-RID.pdf       *)
(* ========================================================================= *)
 
needs "Examples/reduct.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of confluence.                                                 *)
(* ------------------------------------------------------------------------- *)

let confluent = define
  `confluent R <=>
        !x y z. RTC R x y /\ RTC R x z ==> ?u. RTC R y u /\ RTC R z u`;;

let confluent_diamond_RTC = prove
 (`!R. confluent R <=> CR(RTC R)`,
  REWRITE_TAC[confluent; CR]);;

(* ------------------------------------------------------------------------- *)
(* Basic term structure: S and K combinators and function application ("%"). *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("%",(20,"left"));;

let cl_INDUCT,cl_RECURSION = define_type "cl = S | K | % cl cl";;

(* ------------------------------------------------------------------------- *)
(* Reduction relation.                                                       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(12,"right"));;

let redn_rules, redn_ind, redn_cases = new_inductive_definition
 `(!x y f. x --> y   ==>    f % x --> f % y) /\
  (!f g x. f --> g   ==>    f % x --> g % x) /\
  (!x y.   K % x % y --> x) /\
  (!f g x. S % f % g % x --> (f % x) % (g % x))`;;

(* ------------------------------------------------------------------------- *)
(* A different, "parallel", reduction relation.                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-||->",(12,"right"));;

let predn_rules, predn_ind, predn_cases = new_inductive_definition
 `(!x. x -||-> x) /\
  (!x y u v. x -||-> y /\ u -||-> v ==> x % u -||-> y % v) /\
  (!x y. K % x % y -||-> x) /\
  (!f g x. S % f % g % x -||-> (f % x) % (g % x))`;;

(* ------------------------------------------------------------------------- *)
(* Abbreviations for their reflexive-transitive closures.                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->*",(12,"right"));;
parse_as_infix("-||->*",(12,"right"));;

let RTCredn = define `(-->*) = RTC(-->)`;;
let RTCpredn = define `(-||->*) = RTC(-||->)`;;

let RTCredn_rules  = REWRITE_RULE[SYM RTCredn]  (ISPEC `(-->)` RTC_RULES);;
let RTCredn_ind    = REWRITE_RULE[SYM RTCredn]  (ISPEC `(-->)` RTC_INDUCT);;
let RTCpredn_rules = REWRITE_RULE[SYM RTCpredn] (ISPEC `(-||->)` RTC_RULES);;
let RTCpredn_ind   = REWRITE_RULE[SYM RTCpredn] (ISPEC `(-||->)` RTC_INDUCT);;

(* ------------------------------------------------------------------------- *)
(* Prove that the two RTCs are actually the same.                            *)
(* ------------------------------------------------------------------------- *)

let RTCredn_RTCpredn = prove
 (`!x y. x -->* y ==> x -||->* y`,
  REWRITE_TAC[RTCredn; RTCpredn] THEN MATCH_MP_TAC RTC_MONO THEN
  MATCH_MP_TAC redn_ind THEN MESON_TAC[predn_rules]);;

let RTCredn_ap_monotonic = prove
 (`!x y. x -->* y ==> !z. x % z -->* y % z /\ z % x -->* z % y`,
  MATCH_MP_TAC RTCredn_ind THEN MESON_TAC[RTCredn_rules; redn_rules]);;

let predn_RTCredn = prove
 (`!x y. x -||-> y ==> x -->* y`,
  MATCH_MP_TAC predn_ind THEN
  MESON_TAC[RTCredn_rules; redn_rules; RTCredn_ap_monotonic]);;

let RTCpredn_RTCredn = prove
 (`!x y. x -||->* y ==> x -->* y`,
  MATCH_MP_TAC RTCpredn_ind THEN MESON_TAC[predn_RTCredn; RTCredn_rules]);;

let RTCpredn_EQ_RTCredn = prove
 (`(-||->*) = (-->*)`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[RTCpredn_RTCredn; RTCredn_RTCpredn]);;

(* ------------------------------------------------------------------------- *)
(* Now prove diamond property for "-||->" reduction.                         *)
(* ------------------------------------------------------------------------- *)

let characterise t =
  SIMP_RULE[distinctness "cl"; injectivity "cl"; GSYM EXISTS_REFL;
            RIGHT_EXISTS_AND_THM; GSYM CONJ_ASSOC; UNWIND_THM1]
   (SPEC t predn_cases);;

let Sx_PREDN = prove
 (`!x y. S % x -||-> y <=> ?z. y = S % z /\ x -||-> z`,
  REWRITE_TAC[characterise `S % x`] THEN
  MESON_TAC[predn_rules; characterise `S`]);;

let Kx_PREDN = prove
 (`!x y. K % x -||-> y <=> ?z. y = K % z /\ x -||-> z`,
  REWRITE_TAC[characterise `K % x`] THEN
  MESON_TAC[predn_rules; characterise `K`]);;

let Kxy_PREDN = prove
 (`!x y z. K % x % y -||-> z <=>
            (?u v. z = K % u % v /\ x -||-> u /\ y -||-> v) \/ z = x`,
  REWRITE_TAC[characterise `K % x % y`] THEN
  MESON_TAC[predn_rules; Kx_PREDN]);;

let Sxy_PREDN = prove
 (`!x y z. S % x % y -||-> z <=>
            ?u v. z = S % u % v /\ x -||-> u /\ y -||-> v`,
  REWRITE_TAC[characterise `S % x % y`] THEN
  MESON_TAC[predn_rules; characterise `S`; Sx_PREDN]);;

let Sxyz_PREDN = prove
 (`!w x y z. S % w % x % y -||-> z <=>
              (?p q r. z = S % p % q % r /\
                       w -||-> p /\ x -||-> q /\ y -||-> r) \/
              z = (w % y) % (x % y)`,
  REWRITE_TAC[characterise `S % w % x % y`] THEN
  MESON_TAC[predn_rules; Sxy_PREDN]);;

let predn_diamond_lemma = prove
 (`!x y. x -||-> y ==> !z. x -||-> z ==> ?u. y -||-> u /\ z -||-> u`,
  ONCE_REWRITE_TAC[TAUT `a ==> b <=> a ==> a /\ b`] THEN
  MATCH_MP_TAC predn_ind THEN SIMP_TAC[predn_rules] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[predn_rules];
    REPEAT STRIP_TAC THEN UNDISCH_THEN `x % u -||-> z`
     (STRIP_ASSUME_TAC o SIMP_RULE[characterise `x % y`]) THENL
     [ASM_MESON_TAC[predn_rules];
      ASM_MESON_TAC[predn_rules];
      SUBGOAL_THEN `?w. y = K % w /\ z -||-> w` MP_TAC;
      SUBGOAL_THEN `?p q. y = S % p % q /\ f -||-> p /\ g -||-> q` MP_TAC] THEN
    ASM_MESON_TAC[Kx_PREDN; Sxy_PREDN; predn_rules];
    REWRITE_TAC[Kxy_PREDN] THEN MESON_TAC[predn_rules];
    REWRITE_TAC[Sxyz_PREDN] THEN MESON_TAC[predn_rules]]);;

let predn_diamond = prove
 (`CR (-||->)`,
  MESON_TAC[CR; predn_diamond_lemma]);;

(* ------------------------------------------------------------------------- *)
(* Hence we have confluence of the main reduction.                           *)
(* ------------------------------------------------------------------------- *)

let confluent_redn = prove
 (`confluent(-->)`,
  MESON_TAC[confluent_diamond_RTC; RTCpredn_EQ_RTCredn; RTCredn; RTCpredn;
            RTC_CR; predn_diamond]);;
