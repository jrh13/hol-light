
(* miscellaneous useful stuff that doesn't fit in anywhere else *)

let pair_map f (x,y) = (f x,f y)

(* module for maps keyed on terms *)
module Termmap = Map.Make (struct type t = term let compare = compare end)

module Litset = Set.Make (struct type t = bool * int let compare = compare end)

let tm_listItems m = List.rev (Termmap.fold (fun k v l -> (k,v)::l) m [])

let print_term t = print_string (string_of_term t)

let print_type ty = print_string (string_of_type ty)

(*FIXME: inefficient to read chars one by one; 1024 can be improved upon*)
let input_all in_ch =
  let rec loop b =
    match
      (try Some (input_char in_ch)
      with End_of_file -> None)
    with
      Some c -> (Buffer.add_char b c; loop b)
    | None -> () in
  let b = Buffer.create 1024 in
  let _ = loop b in
  Buffer.contents b

let QUANT_CONV conv  = RAND_CONV(ABS_CONV conv)

let BINDER_CONV conv = ABS_CONV conv ORELSEC QUANT_CONV conv

let rec LAST_FORALL_CONV c tm =
  if is_forall (snd (dest_forall tm))
  then
    BINDER_CONV (LAST_FORALL_CONV c) tm
  else c tm

let FORALL_IMP_CONV tm =
  let (bvar,bbody) = dest_forall tm in
  let (ant,conseq) = dest_imp bbody in
  let fant = free_in bvar ant in
  let fconseq =  free_in bvar conseq in
  let ant_thm = ASSUME ant in
  let tm_thm = ASSUME tm in
  if (fant && fconseq)
  then failwith("FORALL_IMP_CONV"^
                ("`"^(fst(dest_var bvar))^"` free on both sides of `==>`"))
  else
    if fant
    then
      let asm = mk_exists(bvar,ant) in
      let th1 = CHOOSE(bvar,ASSUME asm) (UNDISCH(SPEC bvar tm_thm)) in
      let imp1 = DISCH tm (DISCH asm th1) in
      let cncl = rand(concl imp1) in
      let th2 = MP (ASSUME cncl) (EXISTS (asm,bvar) ant_thm) in
      let imp2 = DISCH cncl (GEN bvar (DISCH ant th2)) in
      IMP_ANTISYM_RULE imp1 imp2
    else
      if fconseq
      then
        let imp1 = DISCH ant(GEN bvar(UNDISCH(SPEC bvar tm_thm))) in
        let cncl = concl imp1 in
        let imp2 = GEN bvar(DISCH ant(SPEC bvar(UNDISCH(ASSUME cncl)))) in
        IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH cncl imp2)
      else
        let asm = mk_exists(bvar,ant) in
        let tmp = UNDISCH (SPEC bvar tm_thm) in
        let th1 = GEN bvar (CHOOSE(bvar,ASSUME asm) tmp) in
        let imp1 = DISCH tm (DISCH asm th1) in
        let cncl = rand(concl imp1) in
        let th2 = SPEC bvar (MP(ASSUME cncl) (EXISTS (asm,bvar) ant_thm)) in
        let imp2 = DISCH cncl (GEN bvar (DISCH ant th2)) in
        IMP_ANTISYM_RULE imp1 imp2

let LEFT_IMP_EXISTS_CONV tm =
   let ant, _ = dest_imp tm in
   let bvar,bdy = dest_exists ant in
   let x' = variant (frees tm) bvar in
   let t' = subst [x',bvar] bdy in
   let th1 = GEN x' (DISCH t'(MP(ASSUME tm)(EXISTS(ant,x')(ASSUME t')))) in
   let rtm = concl th1 in
   let th2 = CHOOSE (x',ASSUME ant) (UNDISCH(SPEC x'(ASSUME rtm))) in
     IMP_ANTISYM_RULE (DISCH tm th1) (DISCH rtm (DISCH ant th2))



(*********** terms **************)

let lrand x = rand (rator x)

let t_tm = `T`;;
let f_tm = `F`;;

let is_T tm = (tm = t_tm)

let is_F tm = (tm = f_tm)

(************ HOL **************)

let rec ERC lt tm =
  if is_comb lt
  then
    let ((ltl,ltr),(tml,tmr)) =
      pair_map dest_comb (lt,tm) in
    (ERC ltl tml)@(ERC ltr tmr)
  else
    if is_var lt
    then [(tm,lt)]
    else []

(* easier REWR_CONV which assumes that the supplied theorem is ground and quantifier free,
   so type instantiation and var capture checks are not needed *)
(* no restrictions on the term argument *)
let EREWR_CONV th tm =
  let lt = lhs(concl th) in
  let il = ERC lt tm in
  INST il th
