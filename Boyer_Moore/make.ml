(* ========================================================================= *)
(* Load in Petros Papapanagiotou's Boyer-Moore code and try examples.        *)
(* ========================================================================= *)

loads "Boyer_Moore/boyer-moore.ml";;

(* ------------------------------------------------------------------------- *)
(* Slight variant of Petros's eval.ml file.                                  *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Shortcuts for the various evaluation versions:                            *)
(* ------------------------------------------------------------------------- *)

let BM = BOYER_MOORE;; (* Pure re-implementation of R.Boulton's work. *)
let BME = BOYER_MOORE_EXT;; (* Extended with early termination heuristics and HOL Light features. *)
let BMR = BOYER_MOORE_RE [];;
let BMG = BOYER_MOORE_GEN [];; (* Further extended with M.Aderhold's generalization techniques. *)
let BMF = BOYER_MOORE_FINAL [];;

let RBM = new_rewrite_rule o BOYER_MOORE;;
let RBME = new_rewrite_rule o BOYER_MOORE_EXT;;
let RBMG = new_rewrite_rule o BOYER_MOORE_GEN [];;

(* ------------------------------------------------------------------------- *)
(* Add a theorem as a new function definition and rewrite rule.              *)
(* Adding it as a rewrite rule should no longer be necessary after the       *)
(* latest (July 2009) bugfixes but it doesn't do any harm either.            *)
(* ------------------------------------------------------------------------- *)

let new_stuff x = (new_def x ; new_rewrite_rule x);;

(* ------------------------------------------------------------------------- *)
(* Test sets extracted from the proven theorems in HOL Light's arith.ml and  *)
(* list.ml.                                                                  *)
(* ------------------------------------------------------------------------- *)

loads "Boyer_Moore/testset/arith.ml";; (* Arithmetic test set *)
loads "Boyer_Moore/testset/list.ml";; (* List test set *)

(* ------------------------------------------------------------------------- *)
(* Reloads all the necessary definitions and rules for the evaluation of the *)
(* test sets above.                                                          *)
(* ------------------------------------------------------------------------- *)

let bm_reset () =

system_defs := [];
system_rewrites := [];

new_stuff ADD;
new_stuff MULT;
new_stuff SUB;
new_stuff LE;
new_stuff LT;
new_stuff GE;
new_stuff GT;
new_rewrite_rule (ARITH_RULE `1=SUC(0)`);
new_stuff EXP;
new_stuff FACT;
new_stuff ODD;
new_stuff EVEN;

new_rewrite_rule NOT_SUC;
new_rewrite_rule SUC_INJ;
new_rewrite_rule PRE;
new_rewrite_rule (prove (`!n. ~(SUC n = n)`, INDUCT_TAC THEN ASM_REWRITE_TAC[SUC_INJ;NOT_SUC]));
new_rewrite_rule (prove (`!a b. a + SUC b = SUC (a + b)`,REPEAT GEN_TAC THEN BMF_TAC[]));

new_stuff HD;
new_stuff TL;
new_stuff APPEND;
new_stuff REVERSE;
new_stuff LENGTH;
new_stuff MAP;
new_stuff LAST;
new_stuff REPLICATE;
new_stuff NULL;
new_stuff ALL;
new_stuff EX;
new_stuff ITLIST;
new_stuff MEM;
new_stuff ALL2_DEF;
new_rewrite_rule ALL2;
new_stuff MAP2_DEF;
new_rewrite_rule MAP2;
new_stuff EL;
new_stuff FILTER;
new_stuff ASSOC;
new_stuff ITLIST2_DEF;
new_rewrite_rule ITLIST2;
new_stuff ZIP_DEF;
new_rewrite_rule ZIP;

new_rewrite_rule NOT_CONS_NIL;
new_rewrite_rule CONS_11 ;;

bm_reset();;

(* ------------------------------------------------------------------------- *)
(* Test functions. They use the Unix library to measure time.                *)
(* Unfortunately this means that they do not load properly in Cygwin.        *)
(* ------------------------------------------------------------------------- *)

#load "unix.cma";;
open Unix;;
open Printf;;


(* ------------------------------------------------------------------------- *)
(* Reference of the remaining theory to be proven. Load a list of theorems   *)
(* that you want the evaluation to run through.                              *)
(* eg. remaining_theory := !mytheory;;                                       *)
(* Then use nexttm (see below) to evaluate one of the BOYER_MOORE_*          *)
(* procedures over the list.                                                 *)
(* ------------------------------------------------------------------------- *)

let remaining_theory = ref ([]:term list);;

let currenttm = ref `p`;;

(* ------------------------------------------------------------------------- *)
(* Tries a theorem-proving procedure f on arg.                               *)
(* Returns a truth value of whether the procedure succeeded in finding a     *)
(* proof and a pair of timestamps taken from the start and the end of the    *)
(* procedure.                                                                *)
(* ------------------------------------------------------------------------- *)

let bm_time f arg =
    let t1=Unix.times () in
       let resu = try (if (can dest_thm (f arg)) then true else false) with Failure _ -> false in
       let t2=Unix.times () in (resu,(t1,t2));;
        (*  printf "User time: %f - system time: %f\n%!" (t2.tms_utime -. t1.tms_utime) (t2.tms_stime -. t1.tms_stime);; *)


(* ------------------------------------------------------------------------- *)
(* Uses bm_time to try a Boyer-Moore theorem-proving procedure f on tm.      *)
(* Prints out all the evaluation information that is collected and returns   *)
(* the list of generalizations made during the proof.                        *)
(* ------------------------------------------------------------------------- *)

let bm_test f tm =
    let pfpt = (print_term tm ; print_newline() ; proof_printer false) in
    let (resu,(t1,t2)) = bm_time f tm in
    let pfpt = proof_printer pfpt in
    printf "Proven: %b - Time: %f - Steps: %d - Inductions: %d - Gen terms: %d - Over gens: %d \\\\\n" resu
(t2.tms_utime -. t1.tms_utime) (fst !bm_steps) (snd !bm_steps) (length !my_gen_terms) (!counterexamples) ;
    !my_gen_terms;;

(* ------------------------------------------------------------------------- *)
(* Another version of bm_test but with a more compact printout.              *)
(* Returns unit ().                                                          *)
(* ------------------------------------------------------------------------- *)

let bm_test2 f tm =
    let pfpt = (print_term tm ; print_newline() ; proof_printer false) in
    let (resu,(t1,t2)) = bm_time f tm in
    let pfpt = proof_printer pfpt in
    printf "& %b & %f & %d & %d & %d & %d \\\\\n" resu (t2.tms_utime -. t1.tms_utime) (fst !bm_steps) (snd !bm_steps) (length !my_gen_terms) (!counterexamples) ;
    ();;

(* ------------------------------------------------------------------------- *)
(* Convenient function for evaluation.                                       *)
(* Uses f to try and prove the next term in !remaining_theory by bm_test2    *)
(* ------------------------------------------------------------------------- *)

let nexttm f =
    if (!remaining_theory = []) then failwith "No more"
    else currenttm := hd !remaining_theory ; remaining_theory := tl !remaining_theory ;
    bm_test2 f !currenttm;;

(* ------------------------------------------------------------------------- *)
(* Reruns evaluation on the same term that was last loaded with nexttm.      *)
(* ------------------------------------------------------------------------- *)

let sametm f = bm_test2 f !currenttm;;


(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Just one example.                                                         *)
(* ------------------------------------------------------------------------- *)

bm_test BME `m + n:num = n + m`;;

(* ------------------------------------------------------------------------- *)
(* Note that these don't all terminate, so need more delicacy really.        *)
(* Should carefully reconstruct the cases in Petros's thesis, also maybe     *)
(* using a timeout.                                                          *)
(* ------------------------------------------------------------------------- *)

(****
do_list (bm_test BME) (!mytheory);;

do_list (bm_test BME) (!mytheory2);;
 ****)
