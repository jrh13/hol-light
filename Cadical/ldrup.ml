(* ========================================================================= *)
(* Translate .lrat proof file into HOL inferences and prove a .cnf formula.  *)
(*                                                                           *)
(* This is designed for the .lrat proofs produced by Cadical; those do not   *)
(* use proper RAT lemmas, and have a particularly clean and simple syntax.   *)
(* This might not work for the .lrat files produced by other provers.        *)
(*                                                                           *)
(* The first argument "amap" is the mapping from .cnf variable numbers to    *)
(* HOL propositions, e.g. 123 |-> `p123:bool`.                               *)
(*                                                                           *)
(* For the _GEN functions there are two filename arguments, one for the CNF  *)
(* problem file and the other for the corresponding LRAT proof file. For the *)
(* non-GEN forms there is a single argument that is the root "filename"      *)
(* for the corresponding CNF file "filename.cnf" and LRAT "filename.lrat".   *)
(*                                                                           *)
(* In all cases, non-absolute filenames are interpreted relative to the      *)
(* directory pointed at by the reference "problem_dir".                      *)
(* ========================================================================= *)

let problem_dir = ref "/tmp";;

let LRAT_PROVE_GEN =
  let ptm = `p:bool` and qtm = `q:bool` in
  let orth = REFL(rator(rator(mk_disj(ptm,ptm)))) in
  let number_clauses =
    let rec aux f n (cl,th) =
      match cl with
        [c] -> (n |-> (c,th)) f
      | c::cs ->
          let th1,th2 = CONJ_PAIR th in
          aux ((n |-> (c,th1)) f) (n + 1) (cs,th2)
      | _ -> failwith "number_clauses: there are no clauses" in
    aux undefined 1 in
  let DEDRUP_RULE =
    let pth = SPEC ptm (TAUT `!p. (~p ==> F) <=> p`) in
    fun th -> EQ_MP (INST [rand(lhand(concl th)),ptm] pth) th in
  let ORIFY (c,th) uths = (-c |-> (th,MK_COMB(orth,th))) uths in
  let EQUIFY =
    let nth = SPEC ptm (TAUT `!p. ~p <=> (p <=> F)`)
    and pth = SPEC ptm (TAUT `!p. p <=> (~p <=> F)`) in
    fun (c,th) uths ->
      let tm = concl th in
      let th' =
        if c < 0 then EQ_MP (INST [rand tm,ptm] nth) th
        else EQ_MP (INST [tm,ptm] pth) th in
      let th'' = MK_COMB(orth,th') in
      (-c |-> (th',th'')) uths in
    let upth_l = SPEC ptm (TAUT `!p. F \/ p <=> p`)
    and upth_r = SPEC ptm (TAUT `!p. p \/ F <=> p`)
    and upth_b = TAUT `F \/ F <=> F` in
  fun amap cnfname lratname ->
    let adjust s =
      if Filename.is_relative s
      then Filename.concat (!problem_dir) s else s in
    let probfile = adjust cnfname and lratfile = adjust lratname in
    let prb = read_dimacs probfile in
    let ctm = term_of_clauses amap prb in
    let nvars = rev_itlist (rev_itlist (max o abs)) prb 0 in
    let upth_l_pos = Array.init (nvars+1)
      (fun v -> if v = 0 then upth_b else INST [amap v,ptm] upth_l)
    and upth_l_neg = Array.init (nvars+1)
      (fun v -> if v = 0 then upth_b else INST [mk_neg(amap v),ptm] upth_l)
    and upth_r_pos = Array.init (nvars+1)
      (fun v -> if v = 0 then upth_b else INST [amap v,ptm] upth_r)
    and upth_r_neg = Array.init (nvars+1)
      (fun v -> if v = 0 then upth_b else INST [mk_neg(amap v),ptm] upth_r) in
    let upth_t_pos = Array.init (nvars+1)
        (fun v -> REFL(rator(lhand(concl(Array.get upth_r_pos v)))))
    and upth_t_neg = Array.init (nvars+1)
        (fun v -> REFL(rator(lhand(concl(Array.get upth_r_neg v))))) in
    let UNITPROP =
      fun uths ->
        let rec conv (cl,tm) =
            match (cl,tm) with
              [c],_ -> (try 0,fst(apply uths c) with Failure _ -> c,REFL tm)
            | (c::cs,Comb(Comb(_,l),r)) ->
                (let rl,rth = conv(cs,r) in
                 try let lth,lth' = apply uths c in
                     let th = MK_COMB(lth',rth) in
                     rl,TRANS th (if rl < 0 then Array.get upth_l_neg (-rl)
                                  else Array.get upth_l_pos rl)
                 with Failure _ ->
                   c,
                (if c < 0 then
                   TRANS (MK_COMB(Array.get upth_t_neg (-c),rth))
                         (Array.get upth_r_neg (-c))
                 else
                   TRANS (MK_COMB(Array.get upth_t_pos c,rth))
                         (Array.get upth_r_pos c)))
            | _ -> failwith "UNITPROP: Sanity check" in
      fun (cl,th) -> let d,th' = conv(cl,concl th) in d,EQ_MP th' th in
    let UNITPROPS cls =
      let rec rule uths pf =
        match pf with
          c::ops -> let p,th = UNITPROP uths (apply cls c) in
                    if p = 0 then th else rule (EQUIFY (p,th) uths) ops
        | [] -> failwith "UNITPROPS: did not reach a contradiction" in
      fun dths -> rule (rev_itlist ORIFY dths undefined) in
    let NEGATE_CLAUSE =
      let pth_lor = UNDISCH(SPECL[ptm;qtm]
       (TAUT `!p q. ~(p \/ q) ==> (p <=> F)`))
      and pth_ror = UNDISCH(SPECL[ptm;qtm] (TAUT `!p q. ~(p \/ q) ==> ~q`))
      and pth_ide = SPEC ptm (TAUT `!p. ~p <=> (p <=> F)`) in
      let nrule (c,th) =
        let Comb(_,t) = concl th in
        -c,EQ_MP (INST [t,ptm] pth_ide) th in
      let rec rule (cl,th) =
        match (cl,concl th) with
          [c],_ -> [nrule(c,th)]
        | (c::cs,Comb(_,Comb(Comb(_,l),r))) ->
            let iptho = INST [l,ptm; r,qtm] in
            let th1 = EQ_MP (DEDUCT_ANTISYM_RULE th (iptho pth_lor)) th
            and th2 = EQ_MP (DEDUCT_ANTISYM_RULE th (iptho pth_ror)) th in
            (-c,th1)::rule (cs,th2)
        | [],_ -> []
        | _ -> failwith "NEGATE_CLAUSE: sanity check" in
      rule in
      let LRAT_ADD (n,cl,pf) cls =
        let ctm = term_of_clause amap cl in
        let ctm' = mk_neg ctm in
        let dths = NEGATE_CLAUSE (cl,ASSUME ctm') in
        let fth = UNITPROPS cls dths pf in
        let th = DEDRUP_RULE(DISCH ctm' fth) in
        (n |-> (cl,th)) cls in
      let rec PROCESS_LRAT fd m cls =
        match (try Some(input_line fd) with End_of_file -> None) with
         Some s ->
           (match String.split_on_char ' ' s with
             ns::"d"::dnums ->
                  let n = int_of_string ns
                  and cls' = rev_itlist (undefine o int_of_string) dnums cls in
                  PROCESS_LRAT fd n cls'
            | ns::clap ->
                  let n = int_of_string ns
                  and clans = map int_of_string clap in
                  let i = index 0 clans in
                  let c,u = chop_list i clans in
                  let cls' = LRAT_ADD (n,c,butlast(tl u)) cls in
                  PROCESS_LRAT fd n cls'
            | _ -> failwith "PROCESS_LRAT: Can't parse input line")
        | None -> apply cls m in
    let cls = number_clauses(prb,ASSUME ctm) in
    let fd =
      try open_in lratfile
      with Sys_error _ -> failwith("LRAT_PROVE: can't open "^lratfile) in
    let _,fth = PROCESS_LRAT fd 0 cls in
    let _ = close_in fd in
    NOT_INTRO(DISCH ctm fth);;

let LRAT_PROVE amap basename =
  LRAT_PROVE_GEN amap (basename^".cnf") (basename^".lrat");;

let LRAT_REFUTE_GEN amap cnfname lratname =
    UNDISCH(NOT_ELIM(LRAT_PROVE_GEN amap cnfname lratname));;

let LRAT_REFUTE amap basename =
   LRAT_REFUTE_GEN amap (basename^".cnf") (basename^".lrat");;
