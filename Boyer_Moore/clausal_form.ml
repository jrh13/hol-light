(******************************************************************************)
(* FILE          : clausal_form.ml                                            *)
(* DESCRIPTION   : Functions for putting a formula into clausal form.         *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 13th May 1991                                              *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 12th October 1992                                          *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : 2008                                                       *)
(******************************************************************************)

let IMP_DISJ_THM = TAUT `!t1 t2. t1 ==> t2 <=> ~t1 \/ t2`;;
let RIGHT_OR_OVER_AND = TAUT `!t1 t2 t3. t2 /\ t3 \/ t1 <=> (t2 \/ t1) /\ (t3 \/ t1)`;;
let LEFT_OR_OVER_AND = TAUT `!t1 t2 t3. t1 \/ t2 /\ t3 <=> (t1 \/ t2) /\ (t1 \/ t3)`;;

(*============================================================================*)
(* Theorems for normalizing Boolean terms                                     *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* EQ_EXPAND = |- (x = y) = ((~x \/ y) /\ (~y \/ x))                          *)
(*----------------------------------------------------------------------------*)

let EQ_EXPAND =
 prove
  (`(x = y) = ((~x \/ y) /\ (~y \/ x))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `y:bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* IMP_EXPAND = |- (x ==> y) = (~x \/ y)                                      *)
(*----------------------------------------------------------------------------*)

let IMP_EXPAND = SPEC `y:bool` (SPEC `x:bool` IMP_DISJ_THM);;

(*----------------------------------------------------------------------------*)
(* COND_EXPAND = |- (x => y | z) = ((~x \/ y) /\ (x \/ z))                    *)
(*----------------------------------------------------------------------------*)

let COND_EXPAND =
 prove
  (`(if x then y else z) = ((~x \/ y) /\ (x \/ z))`,
   BOOL_CASES_TAC `x:bool` THEN
   BOOL_CASES_TAC `y:bool` THEN
   BOOL_CASES_TAC `z:bool` THEN
   REWRITE_TAC []);;

(*----------------------------------------------------------------------------*)
(* NOT_NOT_NORM = |- ~~x = x                                                  *)
(*----------------------------------------------------------------------------*)

let NOT_NOT_NORM = SPEC `x:bool` (CONJUNCT1 NOT_CLAUSES);;

(*----------------------------------------------------------------------------*)
(* NOT_CONJ_NORM = |- ~(x /\ y) = (~x \/ ~y)                                  *)
(*----------------------------------------------------------------------------*)

let NOT_CONJ_NORM = CONJUNCT1 (SPEC `y:bool` (SPEC `x:bool` DE_MORGAN_THM));;

(*----------------------------------------------------------------------------*)
(* NOT_DISJ_NORM = |- ~(x \/ y) = (~x /\ ~y)                                  *)
(*----------------------------------------------------------------------------*)

let NOT_DISJ_NORM = CONJUNCT2 (SPEC `y:bool` (SPEC `x:bool` DE_MORGAN_THM));;

(*----------------------------------------------------------------------------*)
(* LEFT_DIST_NORM = |- x \/ (y /\ z) = (x \/ y) /\ (x \/ z)                   *)
(*----------------------------------------------------------------------------*)

let LEFT_DIST_NORM =
 SPEC `z:bool` (SPEC `y:bool` (SPEC `x:bool` LEFT_OR_OVER_AND));;

(*----------------------------------------------------------------------------*)
(* RIGHT_DIST_NORM = |- (x /\ y) \/ z = (x \/ z) /\ (y \/ z)                  *)
(*----------------------------------------------------------------------------*)

let RIGHT_DIST_NORM =
 SPEC `y:bool` (SPEC `x:bool` (SPEC `z:bool` RIGHT_OR_OVER_AND));;

(*----------------------------------------------------------------------------*)
(* CONJ_ASSOC_NORM = |- (x /\ y) /\ z = x /\ (y /\ z)                         *)
(*----------------------------------------------------------------------------*)

let CONJ_ASSOC_NORM =
 SYM (SPEC `z:bool` (SPEC `y:bool` (SPEC `x:bool` CONJ_ASSOC)));;

(*----------------------------------------------------------------------------*)
(* DISJ_ASSOC_NORM = |- (x \/ y) \/ z = x \/ (y \/ z)                         *)
(*----------------------------------------------------------------------------*)

let DISJ_ASSOC_NORM =
 SYM (SPEC `z:bool` (SPEC `y:bool` (SPEC `x:bool` DISJ_ASSOC)));;

(*============================================================================*)
(* Conversions for rewriting Boolean terms                                    *)
(*============================================================================*)

let COND_EXPAND_CONV = REWR_CONV COND_EXPAND;;
let CONJ_ASSOC_NORM_CONV = REWR_CONV CONJ_ASSOC_NORM;;
let DISJ_ASSOC_NORM_CONV = REWR_CONV DISJ_ASSOC_NORM;;
let EQ_EXPAND_CONV = REWR_CONV EQ_EXPAND;;
let IMP_EXPAND_CONV = REWR_CONV IMP_EXPAND;;
let LEFT_DIST_NORM_CONV = REWR_CONV LEFT_DIST_NORM;;
let NOT_CONJ_NORM_CONV = REWR_CONV NOT_CONJ_NORM;;
let NOT_DISJ_NORM_CONV = REWR_CONV NOT_DISJ_NORM;;
let NOT_NOT_NORM_CONV = REWR_CONV NOT_NOT_NORM;;
let RIGHT_DIST_NORM_CONV = REWR_CONV RIGHT_DIST_NORM;;

(*----------------------------------------------------------------------------*)
(* NOT_CONV : conv                                                            *)
(*                                                                            *)
(*    |- !t. ~~t = t                                                          *)
(*    |- ~T = F                                                               *)
(*    |- ~F = T                                                               *)
(*----------------------------------------------------------------------------*)

let NOT_CONV =
try (
 let [th1;th2;th3] = CONJUNCTS NOT_CLAUSES
 in fun tm ->
 (let arg = dest_neg tm
  in  if (is_T arg) then th2
      else if (is_F arg) then th3
      else SPEC (dest_neg arg) th1
 )
) with Failure _ -> failwith "NOT_CONV";;

(*----------------------------------------------------------------------------*)
(* AND_CONV : conv                                                            *)
(*                                                                            *)
(*    |- T /\ t = t                                                           *)
(*    |- t /\ T = t                                                           *)
(*    |- F /\ t = F                                                           *)
(*    |- t /\ F = F                                                           *)
(*    |- t /\ t = t                                                           *)
(*----------------------------------------------------------------------------*)

let AND_CONV =
try (
 let [th1;th2;th3;th4;th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
 in fun tm ->
 (let (arg1,arg2) = dest_conj tm
  in  if (is_T arg1) then SPEC arg2 th1
      else if (is_T arg2) then SPEC arg1 th2
      else if (is_F arg1) then SPEC arg2 th3
      else if (is_F arg2) then SPEC arg1 th4
      else if (arg1 = arg2) then SPEC arg1 th5
      else failwith ""
  )
 ) with Failure _ -> failwith "AND_CONV" ;;

(*----------------------------------------------------------------------------*)
(* OR_CONV : conv                                                             *)
(*                                                                            *)
(*    |- T \/ t = T                                                           *)
(*    |- t \/ T = T                                                           *)
(*    |- F \/ t = t                                                           *)
(*    |- t \/ F = t                                                           *)
(*    |- t \/ t = t                                                           *)
(*----------------------------------------------------------------------------*)

let OR_CONV =
try (
 let [th1;th2;th3;th4;th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
 in fun tm ->
 (let (arg1,arg2) = dest_disj tm
  in  if (is_T arg1) then SPEC arg2 th1
      else if (is_T arg2) then SPEC arg1 th2
      else if (is_F arg1) then SPEC arg2 th3
      else if (is_F arg2) then SPEC arg1 th4
      else if (arg1 = arg2) then SPEC arg1 th5
      else failwith ""
 )
) with Failure _ -> failwith "OR_CONV";;

(*============================================================================*)
(* Conversions for obtaining `clausal' form                                   *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* EQ_IMP_COND_ELIM_CONV : (term -> bool) -> conv                             *)
(*                                                                            *)
(* Eliminates Boolean equalities, Boolean conditionals, and implications from *)
(* terms consisting of =,==>,COND,/\,\/,~ and atoms. The atoms are specified  *)
(* by the predicate that the conversion takes as its first argument.          *)
(*----------------------------------------------------------------------------*)

let rec EQ_IMP_COND_ELIM_CONV is_atom tm =
try
 (if (is_atom tm) then ALL_CONV tm
  else if (is_neg tm) then (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)) tm
  else if (is_eq tm) then
     ((RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) THENC
      (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)) THENC
      EQ_EXPAND_CONV) tm
  else if (is_imp tm) then
     ((RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) THENC
      (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)) THENC
      IMP_EXPAND_CONV) tm
  else if (is_cond tm) then
     ((RATOR_CONV
        (RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)))) THENC
      (RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) THENC
      (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom)) THENC
      COND_EXPAND_CONV) tm
  else ((RATOR_CONV (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) THENC
        (RAND_CONV (EQ_IMP_COND_ELIM_CONV is_atom))) tm
 ) with Failure _ -> failwith "EQ_IMP_COND_ELIM_CONV";;

(*----------------------------------------------------------------------------*)
(* MOVE_NOT_DOWN_CONV : (term -> bool) -> conv -> conv                        *)
(*                                                                            *)
(* Moves negations down through a term consisting of /\,\/,~ and atoms. The   *)
(* atoms are specified by a predicate (first argument). When a negation has   *)
(* reached an atom, the conversion `conv' (second argument) is applied to the *)
(* negation of the atom. `conv' is also applied to any non-negated atoms      *)
(* encountered. T and F are eliminated.                                       *)
(*----------------------------------------------------------------------------*)

let rec MOVE_NOT_DOWN_CONV is_atom conv tm =
try
 (if (is_atom tm) then (conv tm)
  else if (is_neg tm)
  then ((let tm' = rand tm
         in  if (is_atom tm') then ((conv THENC (TRY_CONV NOT_CONV)) tm)
             else if (is_neg tm') then (NOT_NOT_NORM_CONV THENC
                                   (MOVE_NOT_DOWN_CONV is_atom conv)) tm
             else if (is_conj tm') then
                (NOT_CONJ_NORM_CONV THENC
                 (RATOR_CONV (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)))
                                                                          THENC
                 (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) THENC
                 (TRY_CONV AND_CONV)) tm
             else if (is_disj tm') then
                (NOT_DISJ_NORM_CONV THENC
                 (RATOR_CONV (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)))
                                                                          THENC
                 (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) THENC
                 (TRY_CONV OR_CONV)) tm
             else failwith ""))
  else if (is_conj tm) then
     ((RATOR_CONV (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv))) THENC
      (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) THENC
      (TRY_CONV AND_CONV)) tm
  else if (is_disj tm) then
     ((RATOR_CONV (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv))) THENC
      (RAND_CONV (MOVE_NOT_DOWN_CONV is_atom conv)) THENC
      (TRY_CONV OR_CONV)) tm
  else failwith ""
 ) with Failure _ -> failwith "MOVE_NOT_DOWN_CONV";;

(*----------------------------------------------------------------------------*)
(* CONJ_LINEAR_CONV : conv                                                    *)
(*                                                                            *)
(* Linearizes conjuncts using the following conversion applied recursively:   *)
(*                                                                            *)
(*    "(x /\ y) /\ z"                                                         *)
(*    ================================                                        *)
(*    |- (x /\ y) /\ z = x /\ (y /\ z)                                        *)
(*----------------------------------------------------------------------------*)

let rec CONJ_LINEAR_CONV tm =
try
 (if ((is_conj tm) && (is_conj (rand (rator tm))))
  then (CONJ_ASSOC_NORM_CONV THENC
        (RAND_CONV (TRY_CONV CONJ_LINEAR_CONV)) THENC
        (TRY_CONV CONJ_LINEAR_CONV)) tm
  else failwith ""
 ) with Failure _ -> failwith "CONJ_LINEAR_CONV";;

(*----------------------------------------------------------------------------*)
(* CONJ_NORM_FORM_CONV : conv                                                 *)
(*                                                                            *)
(* Puts a term involving /\ and \/ into conjunctive normal form. Anything     *)
(* other than /\ and \/ is taken to be an atom and is not processed.          *)
(*                                                                            *)
(* The conjunction returned is linear, i.e. the conjunctions are associated   *)
(* to the right. Each conjunct is a linear disjunction.                       *)
(*----------------------------------------------------------------------------*)

let rec CONJ_NORM_FORM_CONV tm =
try
 (if (is_disj tm) then
     (if (is_conj (rand (rator tm))) then
         ((RATOR_CONV
              (RAND_CONV ((RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
                          (RAND_CONV CONJ_NORM_FORM_CONV)))) THENC
          (RAND_CONV CONJ_NORM_FORM_CONV) THENC
          RIGHT_DIST_NORM_CONV THENC
          (RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
          (RAND_CONV CONJ_NORM_FORM_CONV) THENC
          (TRY_CONV CONJ_LINEAR_CONV)) tm
      else if (is_conj (rand tm)) then
         ((RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
          (RAND_CONV ((RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
                      (RAND_CONV CONJ_NORM_FORM_CONV))) THENC
          LEFT_DIST_NORM_CONV THENC
          (RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
          (RAND_CONV CONJ_NORM_FORM_CONV) THENC
          (TRY_CONV CONJ_LINEAR_CONV)) tm
      else if (is_disj (rand (rator tm))) then
         (DISJ_ASSOC_NORM_CONV THENC CONJ_NORM_FORM_CONV) tm
      else (let th = RAND_CONV CONJ_NORM_FORM_CONV tm
            in  let tm' = rhs (concl th)
            in  if (is_conj (rand tm'))
                then (TRANS th (CONJ_NORM_FORM_CONV tm'))
                else th))
  else if (is_conj tm) then
     ((RATOR_CONV (RAND_CONV CONJ_NORM_FORM_CONV)) THENC
      (RAND_CONV CONJ_NORM_FORM_CONV) THENC
      (TRY_CONV CONJ_LINEAR_CONV)) tm
  else ALL_CONV tm
 ) with Failure _ -> failwith "CONJ_NORM_FORM_CONV";;

(*----------------------------------------------------------------------------*)
(* has_boolean_args_and_result : term -> bool                                 *)
(*                                                                            *)
(* Yields true if and only if the term is of type ":bool", and if it is a     *)
(* function application, all the arguments are of type ":bool".               *)
(*----------------------------------------------------------------------------*)

let has_boolean_args_and_result tm =
try
 (let args = snd (strip_comb tm)
  in  let types = (type_of tm)::(map type_of args)
  in  (subtract (setify types) [`:bool`]) = [] )
 with Failure _ -> (type_of tm = `:bool`);;

(*----------------------------------------------------------------------------*)
(* CLAUSAL_FORM_CONV : conv                                                   *)
(*                                                                            *)
(* Puts into clausal form terms consisting of =,==>,COND,/\,\/,~ and atoms.   *)
(*----------------------------------------------------------------------------*)

let CLAUSAL_FORM_CONV tm =
try (
 let is_atom tm =
    (not (has_boolean_args_and_result tm)) || (is_var tm) || (is_const tm)
 in
 ((EQ_IMP_COND_ELIM_CONV is_atom) THENC
  (MOVE_NOT_DOWN_CONV is_atom ALL_CONV) THENC
  CONJ_NORM_FORM_CONV) tm
 ) with Failure _ -> failwith "CLAUSAL_FORM_CONV";;
