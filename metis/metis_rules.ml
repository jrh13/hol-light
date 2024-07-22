module Metis_rules = struct

(* move a literal in the proof of a disjunction to the first position
   may not preserve the order of the other literals *)
let FRONT lit thm =
  let conc = concl thm in
  let disj = disjuncts (concl thm) in
  let rest = match partition (fun l -> l = lit) disj with
             | ([], _) -> failwith "FRONT: literal not in disjunction"
             | (_ , r) -> r in
  let disj' = lit :: rest in
  let conc' = list_mk_disj disj' in
  let eq = DISJ_ACI_RULE (mk_eq (conc, conc')) in
  (PURE_ONCE_REWRITE_RULE [eq] thm, rest)
;;

(* resolve two clauses, where atom has to appear at the first position of
   both clauses: positive in the first and negative in the second clause *)
let RESOLVE_N =
  let RESOLVE_1  = TAUT `!a. a ==> ~a ==> F`
  and RESOLVE_2L = TAUT `!a b. a \/ b ==> ~a ==> b`
  and RESOLVE_2R = TAUT `!a c. a ==> ~a \/ c ==> c`
  and RESOLVE_3  = TAUT `!a b c. a \/ b ==> ~a \/ c ==> b \/ c` in
  fun atom -> function
  | ([], []) -> SPEC atom RESOLVE_1
  | (r1, []) -> SPECL [atom; list_mk_disj r1] RESOLVE_2L
  | ([], r2) -> SPECL [atom; list_mk_disj r2] RESOLVE_2R
  | (r1, r2) -> SPECL [atom; list_mk_disj r1; list_mk_disj r2] RESOLVE_3
;;

(* resolve two clauses th1 and th2, where atom appears somewhere
   positive in th1 and negative in th2 *)
let RESOLVE atom th1 th2 =
  (*print_endline ("Atom: " ^ string_of_term atom);
  print_endline ("th1 : " ^ string_of_term (concl th1));
  print_endline ("th2 : " ^ string_of_term (concl th2));*)
  try let (th1', r1) = FRONT atom th1
      and (th2', r2) = FRONT (mk_neg atom) th2 in
      let res = RESOLVE_N atom (r1, r2) in
      MP (MP res th1') th2'
  with _ -> failwith "resolve"
;;

(* given A,  tm |- C, prove A |- ~tm \/ C or
   given A, ~tm |- C, prove A |-  tm \/ C *)
let DISCH_DISJ =
  let IMPL_NOT_L = TAUT `!a b. ~a ==> b <=>  a \/ b`
  and IMPL_NOT_R = TAUT `!a b.  a ==> b <=> ~a \/ b` in
  fun tm th ->
    let impl = DISCH tm th
    and (tm', IMPL_NOT) =
      try dest_neg tm, IMPL_NOT_L
      with _ ->    tm, IMPL_NOT_R in
    let eq = SPECL [tm'; concl th] IMPL_NOT in
    PURE_ONCE_REWRITE_RULE [eq] impl
;;

(* given A, tm1, .., tmn |- th, prove A |- ~tm1 \/ .. \/ ~tmn \/ th *)
let DISCH_DISJS tms th = List.foldr DISCH_DISJ tms th
;;

end (* struct Metis_rules *)
;;
