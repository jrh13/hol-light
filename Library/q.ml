(* ========================================================================= *)
(* A library whose purpose is to remove type annotations from tactics when   *)
(* types can be found from the context.                                      *)
(* Similar to the Q module of HOL4 (<http://hol.sourceforge.net/             *)
(*   kananaskis-8-helpdocs/help/src-sml/htmlsigs/Q.html>).                   *)
(*                                                                           *)
(*            (c) Copyright, Vincent Aravantinos 2012-2013,                  *)
(*                           Hardware Verification Group,                    *)
(*                           Concordia University                            *)
(*                                                                           *)
(*                Contact:   <vincent@encs.concordia.ca>                     *)
(*                                                                           *)
(*            Distributed under the same license as HOL Light.               *)
(* ========================================================================= *)

(* As can be seen in the below signature, all the functions have the same
 * signature as their standard HOL-Light counterpart, except the type "term"
 * is replaced by "string". We do not provide any documentation since their
 * functionality is exactly the same.
 *
 * Note: string arguments should be filled in using the usual term syntax
 * except that backslahses shall be doubled, e.g. `A /\ B` must be
 * written "A /\\ B". Most of the times, this should not be needed anyway.
 *
 * Functions like REAL_ARITH, ARITH_RULE, etc. are also overloaded here, again
 * with the goal of not having to write inferrable annotations: often, when one
 * wants to prove a theorem about reals using REAL_ARITH, (s)he has to annotate
 * his/her goal with `:real` whereas it should be obvious that REAL_ARITH is
 * only called for facts dealing with reals.
 *
 * Ex:
 *   The goal:
 *
 *   # g `!x:real. P x ==> ?y. P y`
 *
 *   can be reduced equivalently by the two following tactics:
 *
 *   # e (REPEAT STRIP_TAC THEN EXISTS_TAC `x:real`)
 *
 *   # e (REPEAT STRIP_TAC THEN Pa.EXISTS_TAC "x")
 *
 * Note:
 *   The module cannot be called "Q" because HOL Light does not allow
 *   modules with a single letter. I choose "Pa", short for "Parse".
 *
 *)


module Pa :
  sig
    val CONTEXT_TAC : ((string * pretype) list -> tactic) -> tactic
    val PARSE_IN_CONTEXT : (term -> tactic) -> (string -> tactic)
    val PARSES_IN_CONTEXT : (term list -> tactic) -> (string list -> tactic)
    val EXISTS_TAC : string -> tactic
    val SUBGOAL_THEN : string -> thm_tactic -> tactic
    val SUBGOAL_TAC : string -> string -> tactic list -> tactic
    val ASM_CASES_TAC : string -> tactic
    val BOOL_CASES_TAC : string -> tactic
    val SPEC_TAC : string * string -> tactic
    val SPEC : string -> thm -> thm
    val SPECL : string list -> thm -> thm
    val GEN : string -> thm -> thm
    val GENL : string list -> thm -> thm
    val X_GEN_TAC : string -> tactic
    val REAL_ARITH : string -> thm
    val REAL_FIELD : string -> thm
    val REAL_RING : string -> thm
    val ARITH_RULE : string -> thm
    val NUM_RING : string -> thm
    val INT_ARITH : string -> thm
    val ABBREV_TAC : string -> tactic
    val call_with_interface : (unit -> 'a) -> (term -> 'b) -> string -> 'b
  end
  =
  struct
    let parse_preterm = fst o parse_preterm o lex o explode

    let CONTEXT_common f hs c x =
      let vs = freesl (c::hs) in
      f (map (fun x -> name_of x, pretype_of_type(type_of x)) vs) x

    let CONTEXT_TAC ttac (asms,c as g) =
      CONTEXT_common ttac (map (concl o snd) asms) c g

    let CONTEXT_RULE r th = CONTEXT_common r (hyp th) (concl th) th

    let PARSES_IN_CONTEXT ttac ss =
      CONTEXT_TAC (fun env ->
        ttac (map (term_of_preterm o retypecheck env o parse_preterm) ss))

    let PARSE_IN_CONTEXT tac s = PARSES_IN_CONTEXT (function [t] -> tac t) [s]

    let type_of_forall = type_of o fst o dest_forall

    let force_type ?(env=[]) s ty =
      let pty = pretype_of_type ty in
      term_of_preterm (retypecheck env (Typing(parse_preterm s,pty)))

    let BOOL_CONTEXT_TAC ttac s =
      CONTEXT_TAC (fun env -> ttac (force_type ~env s bool_ty))

    let SUBGOAL_THEN s ttac = BOOL_CONTEXT_TAC (C SUBGOAL_THEN ttac) s
    let SUBGOAL_TAC l s tacs = BOOL_CONTEXT_TAC (C (SUBGOAL_TAC l) tacs) s
    let ABBREV_TAC = BOOL_CONTEXT_TAC ABBREV_TAC

    let ASM_CASES_TAC = BOOL_CONTEXT_TAC ASM_CASES_TAC
    let BOOL_CASES_TAC = BOOL_CONTEXT_TAC BOOL_CASES_TAC

    let EXISTS_TAC s (_,c as g) =
      CONTEXT_TAC (fun env ->
        EXISTS_TAC (force_type ~env s (type_of (fst (dest_exists c))))) g

    let SPEC_TAC (u,x) =
      PARSE_IN_CONTEXT (fun u' -> SPEC_TAC (u',force_type x (type_of u'))) u

    let SPEC s th =
      CONTEXT_RULE (fun env ->
        SPEC (force_type ~env s (type_of_forall (concl th)))) th

    let SPECL tms th =
      try rev_itlist SPEC tms th with Failure _ -> failwith "SPECL"

    let GEN s th =
      GEN (try find ((=) s o name_of) (frees (concl th)) with _ -> parse_term s)
        th

    let GENL = itlist GEN

    let X_GEN_TAC s (_,c as g) = X_GEN_TAC (force_type s (type_of_forall c)) g

    let call_with_interface p f s =
      let i = !the_interface in
      p ();
      let res = f (parse_term s) in
      the_interface := i;
      res

    let [REAL_ARITH;REAL_FIELD;REAL_RING] =
      map (call_with_interface prioritize_real)
          [REAL_ARITH;REAL_FIELD;REAL_RING]
    let [ARITH_RULE;NUM_RING] =
      map (call_with_interface prioritize_num) [ARITH_RULE;NUM_RING]
    let INT_ARITH = call_with_interface prioritize_int INT_ARITH
  end;;

(* You can add the following if complex theories are loaded:
module Pa =
  struct
    include Pa
    let COMPLEX_FIELD = call_with_interface prioritize_complex COMPLEX_FIELD;;
    let SIMPLE_COMPLEX_ARITH =
      call_with_interface prioritize_complex SIMPLE_COMPLEX_ARITH;
  end;; *)
