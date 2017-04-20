(*open satCommonTools dimacsTools;; *)

(* parse minisat proof log into array cl.
   array elements are either root clauses or
   resolution chains for deriving the learnt clauses.
   Last chain derives empty clause  *)

type rootc =
    Rthm of thm * Litset.t * term * thm
  | Ll of term * Litset.t

type clause =
    Blank
  | Chain of (int * int) list * int (* var, cl index list and the length of that list *)
  | Root of rootc
  | Learnt of thm * Litset.t (* clause  thm, lits as nums set *)

let sat_fileopen s = open_in_bin s

let sat_fileclose is = close_in is

let sat_getChar is = Int32.of_int(input_byte is)

(* copied from Minisat-p_v1.14::File::getUInt*)
(* this is technically able to parse int32's but no *)
(* point since we return int's always *)
(* FIXME: no idea what will happen on a 64-bit arch *)
let sat_getint is =
  let (land) = Int32.logand in
  let (lor) = Int32.logor in
  let (lsl) = Int32.shift_left in
  let (lsr) = Int32.shift_right in
  let byte0 = sat_getChar is in
  if ((byte0 land (Int32.of_int 0x80))=(Int32.of_int 0x0)) (* 8 *)
  then Int32.to_int(byte0)
  else
    match Int32.to_int((byte0 land (Int32.of_int 0x60)) lsr 5) with
      0 ->
        let byte1 = sat_getChar is in
        Int32.to_int(((byte0 land (Int32.of_int 0x1F)) lsl 8) lor byte1) (* 16 *)
    | 1 ->
        let byte1 = sat_getChar is in
        let byte2 = sat_getChar is in
        Int32.to_int( (((byte0 land (Int32.of_int 0x1F)) lsl 16) lor (byte1 lsl 8)) lor byte2)
    | 2 ->
        let byte1 = sat_getChar is in
        let byte2 = sat_getChar is in
        let byte3 = sat_getChar is in
        Int32.to_int(((((byte0 land (Int32.of_int 0x1F)) lsl 24) lor (byte1 lsl 16))
                 lor (byte2 lsl 8)) lor byte3)
    (* default case is only where int64 is needed since we do a lsl 32*)
    | _ ->
        let byte0 = sat_getChar is in
        let byte1 = sat_getChar is in
        let byte2 = sat_getChar is in
        let byte3 = sat_getChar is in
        let byte4 = sat_getChar is in
        let byte5 = sat_getChar is in
        let byte6 = sat_getChar is in
        let byte7 = sat_getChar is in
        Int32.to_int((((byte0 lsl 24) lor (byte1 lsl 16) lor (byte2 lsl 8) lor byte3) lsl 32)
                       lor  ((byte4 lsl 24) lor (byte5 lsl 16) lor (byte6 lsl 8) lor byte7))

let isRootClauseIdx cl ci =
  match Array.get cl ci with
    Root _ -> true
  | _      -> false

(* p is a literal *)
(* this mapping allows shadow ac-normalisation which keeps the lits for a given var together *)
(* the -1 is because literalToInt returns HolSatLib var numbers (base 1) *)
let literalToInt2 p =
  let (sign,vnum) = literalToInt p in
  2*(vnum-1)+(if sign then 1 else 0)

let literalToInt3 p =
  let (sign,vnum) = literalToInt p in
  (sign,vnum-1)

(* parse a root clause *)
let getIntRoot fin idx =
  let rec loop idx' acc =
    let v = sat_getint fin in
    if v=0
    then idx::(List.rev acc)
    else loop (idx'+v) ((idx'+v)::acc) in
  let res = loop idx [] in
  res

(*l1 and l2 are number reps of lits. Are they complements? *)
let is_compl l1 l2 = (abs(l2-l1)=1) && (l1 mod 2 = 0)

(*il is clause input from minisat proof trace,
  sl is internal clause sorted and unduped, with diff in var numbering account for *)
(* thus if il and sl are not exactly the same,
   then the clause represented by sl was skipped *)
let isSameClause (il,sl) = (Pervasives.compare il sl = 0)

let rec getNextRootClause scl vc cc lr il rcv =
  let rc = Array.get rcv lr in
  let rcl = disjuncts rc in
  let lnl = List.map literalToInt3 rcl in
  let lns =
    List.fold_left (fun s e -> Litset.add e s)
      Litset.empty lnl in
  let slnl = (* FIXME: speed this up*)
    List.sort Pervasives.compare
      (setify
         (List.map (fun (isn,vi) ->
           if isn
           then 2*vi+1
           else 2*vi) lnl)) in
  if isSameClause(il,slnl)
  then (Array.set scl lr cc;(lr,(rc,lns)))
  else getNextRootClause scl vc cc (lr+1) il rcv

(* this advances the file read pointer but we pick up the
   actual clause from the list of clauses we already have
   this is because minisatp removes duplicate literals
   and sorts the literals so I can't efficiently find the
   corresponding clause term in HOL.
   assert: minisatp logs the root clauses in order of input*)
let addClause scl vc cc lr rcv fin sr lit1 =
    let l = getIntRoot fin (lit1 lsr 1) in
    let res =
      match l with
        []  -> failwith ("addClause:Failed parsing clause "^(string_of_int (cc))^"\n")
      | _   ->
          let (lr,(t,lns)) =
            getNextRootClause scl vc cc lr l rcv in
          (cc+1,lr+1,(Root (Ll (t,lns)))::sr) in
    res

(* parse resolve chain *)
let getIntBranch fin id h =
  let rec loop acc len =
    (*-1 is purely a decoding step *)
    (* (i.e. not translating b/w HolSat and ms)*)
    let v = (sat_getint fin)-1 in
    if v=(-1)
    then ((v,h)::(List.rev acc),len+1)
    else
      let ci = id-(sat_getint fin) in
      loop ((v,ci)::acc) (len+1) in
  let res = loop [] 0 in
  res

let addBranch fin sr cc id tc =
    let (br,brl) =
      getIntBranch fin id (id-(tc lsr 1)) in
    let res =
      if brl=1 (*(tl br = []) *)
      then (cc,false,sr) (* delete *)
      else (cc+1,true,(Chain (br,brl))::sr) (* resolve *) in
    res

(*this is modelled on MiniSat::Proof::traverse,
  except we first read in everything then resolve backwards *)
(*sr is stack for originally reading in the clauses *)
(*lr is unskipped root clause count. *)
(*cc is clause count (inc learnt) *)

let rec readTrace_aux scl vc cc lr rcv fin sr id =
  let tmp,eof = try sat_getint fin,false with End_of_file -> 42,true in
  if eof then (cc,sr) else
  if (tmp land 1)=0
  then
    let (cc,lr,sr) =
      addClause scl vc cc lr rcv fin sr tmp in
    readTrace_aux scl vc cc lr rcv fin sr (id+1)
  else
    let (cc,isch,sr') =
      addBranch fin sr cc id tmp in
    if isch
    then readTrace_aux scl vc cc lr rcv fin sr' (id+1) (* chain *)
    else readTrace_aux scl vc cc lr rcv fin sr' id  (* deletion *)
;;

(*fill in the root clause and chain array*)
let parseTrace nr fname vc rcv =
    try
      let fin = sat_fileopen fname in
      let scl = Array.make nr (-1) in (*cl[scl[i]]=rcv[i] or scl[i]=~1 if rcv[i] was trivial *)
      let (cc,sr) = readTrace_aux scl vc 0 0 rcv fin [] 0 in
      let _ = sat_fileclose fin in
      Some (cc,sr,scl)
    with Sys_error _  -> None

let getChain = function
    Chain (vcl,vcll) -> vcl
  |  _ ->  failwith("getChain: not a Chain")

(*make backwards pass through cl, returning only the chains actually used in deriving F*)
let rec mk_sk cl ca ci =
    let ch = List.fold_left
        (fun ch (v,cci) ->
          if (Array.get ca cci) || (isRootClauseIdx cl cci)
          then ch
          else (mk_sk cl ca cci)::ch)
        [] (getChain (Array.get cl ci)) in
    (Array.set ca ci true;ci::(List.concat ch))

let parseMinisatProof nr fname vc rcv =
    match parseTrace nr fname vc rcv with
      Some (cc,sr,scl) ->
        let srl = List.length sr in
        (*stores clauses as root clauses, learnt clauses or unresolved chains *)
        let cl = Array.make srl Blank in
        let _ = List.fold_left (fun i c -> (Array.set cl (i-1) c;i-1)) cc sr in
        let sk = mk_sk cl (Array.make srl false) (cc-1) in
        Some (cl,sk,scl,srl,cc)
    | None -> None
