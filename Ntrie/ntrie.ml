(* ========================================================================= *)
(* Computing with finite sets of numerals.                                   *)
(*                                                                           *)
(*        (c) Copyright, Clelia Lomuto, Marco Maggesi, 2009.                 *)
(*          Distributed with HOL Light under same license terms              *)
(*                                                                           *)
(* This file provides some conversions that operate on finite sets of        *)
(* numerals represented as a trie-like structure (here called "ntries").     *)
(*                                                                           *)
(* A concrete syntax for ntries is made available after loading this file.   *)
(*                                                                           *)
(* Examples:                                                                 *)
(*                                                                           *)
(* # NTRIE_REDUCE_CONV `%%(10 1001 3) INTER %%(3 7 10) UNION %%(3 100)`;;    *)
(* val it : thm =                                                            *)
(*   |- %%(3 10 1001) INTER %%(3 7 10) UNION %%(3 100) = %%(3 10 100)        *)
(*                                                                           *)
(* NTRIE_REDUCE_CONV                                                         *)
(*   `%%(10 1001 3) INTER %%(3 7 10) SUBSET %%(10 23) UNION %%(3 33)`;;      *)
(* val it : thm =                                                            *)
(*   |- %%(3 10 1001) INTER %%(3 7 10) SUBSET %%(10 23) UNION %%(3 33) <=> T *)
(*                                                                           *)
(* The code in this file is divided into three main parts:                   *)
(*     1. Definitions and theorems.                                          *)
(*     2. Syntax extension for ntries.                                       *)
(*     3. Rules and conversions.                                             *)
(* ========================================================================= *)


(* ========================================================================= *)
(* First part: Definitions and theorems.                                     *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Constructors for the ntrie representation of a set of numerals.           *)
(* ------------------------------------------------------------------------- *)

let NTRIE  = new_definition `NTRIE s:num->bool = s`
and NEMPTY = new_definition `NEMPTY:num->bool = {}`
and NZERO  = new_definition `NZERO = {_0}`
and NNODE  = new_definition `NNODE s t = IMAGE BIT0 s UNION IMAGE BIT1 t`;;

let NTRIE_RELATIONS = prove
 (`NNODE NEMPTY NEMPTY = NEMPTY /\
   NNODE NZERO  NEMPTY = NZERO`,
  REWRITE_TAC[NEMPTY; NZERO; NNODE] THEN SET_TAC[ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Membership.                                                               *)
(* ------------------------------------------------------------------------- *)

let NTRIE_IN = prove
 (`(!s n. NUMERAL n IN NTRIE s <=> n IN s) /\
   (!n. ~(n IN NEMPTY)) /\
   (!n. n IN NZERO <=> n = _0) /\
   (!s t. _0 IN NNODE s t <=> _0 IN s) /\
   (!s t n. BIT0 n IN NNODE s t <=> n IN s) /\
   (!s t n. BIT1 n IN NNODE s t <=> n IN t)`,
  REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE] THEN SET_TAC[ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Inclusion.                                                                *)
(* ------------------------------------------------------------------------- *)

let NTRIE_SUBSET = prove
 (`(!s t. NTRIE s SUBSET NTRIE t <=> s SUBSET t) /\
   (!s. NEMPTY SUBSET s) /\
   (!s:num->bool. s SUBSET s) /\
   ~(NZERO SUBSET NEMPTY) /\
   (!s t. NNODE s t SUBSET NEMPTY <=> s SUBSET NEMPTY /\ t SUBSET NEMPTY) /\
   (!s t. NNODE s t SUBSET NZERO <=> s SUBSET NZERO /\ t SUBSET NEMPTY) /\
   (!s t. NZERO SUBSET NNODE s t <=> NZERO SUBSET s) /\
   (!s1 s2 t1 t2.
      NNODE s1 t1 SUBSET NNODE s2 t2 <=> s1 SUBSET s2 /\ t1 SUBSET t2)`,
  REWRITE_TAC[NTRIE; NEMPTY; NZERO; NNODE; SUBSET; FORALL_IN_UNION;
              FORALL_IN_IMAGE; FORALL_IN_INSERT] THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equality.                                                                 *)
(* ------------------------------------------------------------------------- *)

let NTRIE_EQ = prove
 (`(!s t. NTRIE s = NTRIE t <=> s = t) /\
   ~(NZERO = NEMPTY) /\
   ~(NEMPTY = NZERO) /\
   (!s t. NNODE s t = NEMPTY <=> s = NEMPTY /\ t = NEMPTY) /\
   (!s t. NEMPTY = NNODE s t <=> s = NEMPTY /\ t = NEMPTY) /\
   (!s t. NNODE s t = NZERO <=> s = NZERO /\ t = NEMPTY) /\
   (!s t. NZERO = NNODE s t <=> s = NZERO /\ t = NEMPTY) /\
   (!s1 s2 t1 t2. NNODE s1 t1 = NNODE s2 t2 <=> s1 = s2 /\ t1 = t2)`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; NTRIE_SUBSET; NEMPTY; NZERO] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Singleton.                                                                *)
(* ------------------------------------------------------------------------- *)

let NTRIE_SING = prove
 (`(!n. {NUMERAL n} = NTRIE {n}) /\
   {_0} = NZERO /\
   (!n. {BIT0 n} = if n = _0 then NZERO else NNODE {n} NEMPTY) /\
   (!n. {BIT1 n} = NNODE NEMPTY {n})`,
  REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Insertion.                                                                *)
(* ------------------------------------------------------------------------- *)

let NTRIE_INSERT = prove
 (`(!s n. NUMERAL n INSERT NTRIE s = NTRIE (n INSERT s)) /\
   _0 INSERT NEMPTY = NZERO /\
   _0 INSERT NZERO = NZERO /\
   (!s t. _0 INSERT NNODE s t = NNODE (_0 INSERT s) t) /\
   (!n. BIT0 n INSERT NZERO = if n = _0 then NZERO else
                              NNODE (n INSERT NZERO) NEMPTY) /\
   (!n. BIT1 n INSERT NZERO = NNODE NZERO {n}) /\
   (!s t n. BIT0 n INSERT NNODE s t = NNODE (n INSERT s) t) /\
   (!s t n. BIT1 n INSERT NNODE s t = NNODE s (n INSERT t))`,
  REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let NTRIE_UNION = prove
 (`(!s t. NTRIE s UNION NTRIE t = NTRIE (s UNION t)) /\
   (!s. s UNION NEMPTY = s) /\
   (!s. NEMPTY UNION s = s) /\
   NZERO UNION NZERO = NZERO /\
   (!s t. NNODE s t UNION NZERO = NNODE (s UNION NZERO) t) /\
   (!s t. NZERO UNION NNODE s t = NNODE (s UNION NZERO) t) /\
   (!s t r q. NNODE s t UNION NNODE r q = NNODE (s UNION r) (t UNION q))`,
 REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE] THEN SET_TAC[ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* Warning: rewriting with this theorem generates ntries which are not       *)
(* "reduced".  It has to be used in conjuction with NTRIE_RELATIONS.         *)
(* ------------------------------------------------------------------------- *)

let NTRIE_INTER = prove
 (`(!s t. NTRIE s INTER NTRIE t = NTRIE (s INTER t)) /\
   (!s. NEMPTY INTER s = NEMPTY) /\
   (!s. s INTER NEMPTY = NEMPTY) /\
   NZERO INTER NZERO = NZERO /\
   (!s t. NZERO INTER NNODE s t = NZERO INTER s) /\
   (!s t. NNODE s t INTER NZERO = NZERO INTER s) /\
   (!s1 s2 t1 t2.
      NNODE s1 t1 INTER NNODE s2 t2 = NNODE (s1 INTER s2) (t1 INTER t2))`,
  REWRITE_TAC[NTRIE; NEMPTY; NZERO; NNODE] THEN SET_TAC[ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Deletion.                                                                 *)
(* Warning: rewriting with this theorem generates ntries which are not       *)
(* "reduced".  It has to be used in conjuction with NTRIE_RELATIONS.         *)
(* ------------------------------------------------------------------------- *)

let NTRIE_DELETE = prove
 (`(!s n. NTRIE s DELETE NUMERAL n = NTRIE (s DELETE n)) /\
   (!n. NEMPTY DELETE n = NEMPTY) /\
   (!n. NZERO DELETE n = if n = _0 then NEMPTY else NZERO) /\
   (!s t. NNODE s t DELETE _0 = NNODE (s DELETE _0) t) /\
   (!s t n. NNODE s t DELETE BIT0 n = NNODE (s DELETE n) t) /\
   (!s t n. NNODE s t DELETE BIT1 n = NNODE s (t DELETE n))`,
  REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[ARITH_EQ; ARITH_ZERO]);;

(* ------------------------------------------------------------------------- *)
(* Disjointedness.                                                           *)
(* ------------------------------------------------------------------------- *)

let NTRIE_DISJOINT = prove
 (`(!s t. DISJOINT (NTRIE s) (NTRIE t) <=> DISJOINT s t) /\
   (!s. DISJOINT s NEMPTY) /\
   (!s. DISJOINT NEMPTY s) /\
   ~DISJOINT NZERO NZERO /\
   (!s t. DISJOINT NZERO (NNODE s t) <=> DISJOINT s NZERO) /\
   (!s t. DISJOINT (NNODE s t) NZERO <=> DISJOINT s NZERO) /\
   (!s1 s2 t1 t2. DISJOINT (NNODE s1 t1) (NNODE s2 t2) <=>
                  DISJOINT s1 s2 /\ DISJOINT t1 t2)`,
  REWRITE_TAC[NTRIE; DISJOINT; GSYM NEMPTY;
              NTRIE_INTER; INTER_ACI; NTRIE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Difference.                                                               *)
(* ------------------------------------------------------------------------- *)

let NTRIE_DIFF = prove
 (`(!s t. NTRIE s DIFF NTRIE t = NTRIE (s DIFF t)) /\
   (!s. NEMPTY DIFF s = NEMPTY) /\
   (!s. s DIFF NEMPTY = s) /\
   NZERO DIFF NZERO = NEMPTY /\
   (!s t. NZERO DIFF NNODE s t = NZERO DIFF s) /\
   (!s t. NNODE s t DIFF NZERO = NNODE (s DIFF NZERO) t) /\
   (!s1 t1 s2 t2. NNODE s1 t1 DIFF NNODE s2 t2 =
                  NNODE (s1 DIFF s2) (t1 DIFF t2))`,
  REWRITE_TAC[NTRIE; NEMPTY; NZERO; NNODE] THEN SET_TAC[ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

let NTRIE_IMAGE_DEF = new_definition
  `!f:num->A acc s. NTRIE_IMAGE f acc s = IMAGE f s UNION acc`;;

let NTRIE_IMAGE = prove
 (`(!f:num->A acc. NTRIE_IMAGE f acc NEMPTY = acc) /\
   (!f:num->A acc. NTRIE_IMAGE f acc NZERO = f _0 INSERT acc) /\
   (!f:num->A acc s t.
      NTRIE_IMAGE f acc (NNODE s t) =
      NTRIE_IMAGE (\n. f (BIT1 n)) (NTRIE_IMAGE (\n. f (BIT0 n)) acc s) t)`,
  REWRITE_TAC[NTRIE; NEMPTY; NZERO; NNODE; NTRIE_IMAGE_DEF] THEN SET_TAC[]);;

let IMAGE_EQ_NTRIE_IMAGE = prove
  (`!f:num->A s. IMAGE f (NTRIE s) = NTRIE_IMAGE (\n. f (NUMERAL n)) {} s`,
   REWRITE_TAC [NUMERAL; NTRIE; ETA_AX; NTRIE_IMAGE_DEF; UNION_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Constructor and destructor for ntries.                                    *)
(* ------------------------------------------------------------------------- *)

let [NTRIE_tm; NEMPTY_tm; NZERO_tm; NNODE_tm] =
  let f = fst o strip_comb o lhs o snd o strip_forall o concl in
  map f [NTRIE; NEMPTY; NZERO; NNODE];;

let mk_nnode = mk_binop NNODE_tm;;

let mk_small_ntrie =
  let rec mk_sing n =
    if n == 0 then NZERO_tm else
    let r,d = n mod 2,n / 2 in
    let tm = mk_sing d in
    if r == 0
    then mk_nnode tm NEMPTY_tm
    else mk_nnode NEMPTY_tm tm in
  let rec part ((el,ol) as acc) =
    function
      [] -> acc
    | h::t -> let acc = let r,d = h mod 2,h / 2 in
                        if r = 0 then (d::el,ol) else (el,d::ol) in
              part acc t in
  let rec recur =
    function
      [] -> NEMPTY_tm
    | [n] -> mk_sing n
    | m::(n::_ as t) when n == m -> recur t
    | s -> let evens,odds = part ([],[]) s in
           mk_nnode (recur evens) (recur odds) in
  fun tm -> mk_comb(NTRIE_tm,recur tm);;

let mk_ntrie =
  let rec mk_sing n =
    if n =/ num_0 then NZERO_tm else
    let r,d = mod_num n num_2,quo_num n num_2 in
    let tm = mk_sing d in
    if r =/ num_0
    then mk_nnode tm NEMPTY_tm
    else mk_nnode NEMPTY_tm tm in
  let rec part ((el,ol) as acc) =
    function
      [] -> acc
    | h::t -> let acc = let r,d = mod_num h num_2,quo_num h num_2 in
                        if r =/ num_0 then (d::el,ol) else (el,d::ol) in
              part acc t in
  let rec recur =
    function
      [] -> NEMPTY_tm
    | [n] -> mk_sing n
    | m::(n::_ as t) when n =/ m -> recur t
    | s -> let evens,odds = part ([],[]) s in
           mk_nnode (recur evens) (recur odds) in
  fun tm -> mk_comb(NTRIE_tm,recur tm);;


(* ========================================================================= *)
(* Second part: Syntax extension for ntries.                                 *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Destructor for ntries.                                                    *)
(* ------------------------------------------------------------------------- *)

let mk_numset tm = mk_setenum(tm,`:num`);;

let dest_small_ntrie,dest_ntrie =
  let ntrie_strip_tag =
    function
      Comb(Const("NTRIE",_),tm) -> tm
    | _ -> failwith "ntrie_strip_tag" in
  let dest_small_ntrie tm =
    let rec runk n =
      function
        [] -> n
      | h::t -> let d = 2*n in runk (if h then d+1 else d) t in
    let rec recur acc k =
      function
        Const("NEMPTY",_) -> acc
      | Const("NZERO",_) -> runk 0 k::acc
      | Comb(Comb(Const("NNODE",_),stm),ttm) ->
          recur (recur acc (false::k) stm) (true::k) ttm
      | _ -> failwith "malformed ntrie" in
    recur [] [] (ntrie_strip_tag tm) in
  let dest_ntrie tm =
    let rec runk n =
      function
        [] -> n
      | h::t -> let d = num_2 */ n in runk (if h then d +/ num_1 else d) t in
    let rec recur acc k =
      function
        Const("NEMPTY",_) -> acc
      | Const("NZERO",_) -> runk num_0 k::acc
      | Comb(Comb(Const("NNODE",_),stm),ttm) ->
          recur (recur acc (false::k) stm) (true::k) ttm
      | _ -> failwith "malformed ntrie" in
    recur [] [] (ntrie_strip_tag tm) in
  dest_small_ntrie,dest_ntrie;;

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let pp_print_ntrie =
  let print_num fmt n = pp_print_string fmt (string_of_num n) in
  let print_nums fmt =
    let rec loop =
      function
        [] -> ()
      | h::t -> pp_print_space fmt (); print_num fmt h; loop t
    in
    function
      [] -> ()
    | h::t -> print_num fmt h; loop t in
  let print fmt tm =
    let l = sort (</) (dest_ntrie tm) in
    pp_open_box fmt 0; pp_print_string fmt "%%(";
    pp_open_box fmt 0; print_nums fmt l; pp_close_box fmt ();
    pp_print_string fmt ")"; pp_close_box fmt () in
  fun fmt ->
    function
      Comb(Const("NTRIE",_),_) as tm -> print fmt tm
    | _ -> failwith "print_ntrie";;

let print_ntrie = pp_print_ntrie std_formatter
and string_of_ntrie = print_to_string pp_print_ntrie;;

install_user_printer("ntrie",pp_print_ntrie);;

(* ------------------------------------------------------------------------- *)
(* Parser.                                                                   *)
(* ------------------------------------------------------------------------- *)

reserve_words["%%"];;

let preparse_ntrie,parse_ntrie =
  let NTRIE_ptm = Varp("NTRIE",dpty)
  and NEMPTY_ptm = Varp("NEMPTY",dpty)
  and NZERO_ptm = Varp("NZERO",dpty)
  and NNODE_ptm = Varp("NNODE",dpty) in
  let pmk_nnode ptm1 ptm2 = Combp(Combp(NNODE_ptm,ptm1),ptm2) in
  let pmk_ntrie =
    let rec pmk_sing n =
      if n =/ num_0 then NZERO_ptm else
      let r,d = mod_num n num_2,quo_num n num_2 in
      let tm = pmk_sing d in
      if r =/ num_0
      then pmk_nnode tm NEMPTY_ptm
      else pmk_nnode NEMPTY_ptm tm in
    let rec part ((el,ol) as acc) =
      function
        [] -> acc
      | h::t -> let acc = let r,d = mod_num h num_2,quo_num h num_2 in
                          if r = num_0 then (d::el,ol) else (el,d::ol) in
                part acc t in
    let rec recur =
      function
        [] -> NEMPTY_ptm
      | [n] -> pmk_sing n
      | m::(n::_ as t) when n =/ m -> recur t
      | s -> let evens,odds = part ([],[]) s in
             pmk_nnode (recur evens) (recur odds) in
    fun tm -> Combp(NTRIE_ptm,recur tm) in
  let parse_int =
    function
      Ident s::rest ->
        let n = try num_of_string s with Failure _ -> raise Noparse in
        n,rest
    | _ -> raise Noparse in
  let parse_ints = many parse_int >> pmk_ntrie in
  let preparse_ntrie =
    ((a(Resword "%%") ++ a(Resword "(") ++ parse_ints) >> snd) ++
    a(Resword ")") >> fst in
  let parse_ntrie s =
    let ptm,l = (preparse_ntrie o lex o explode) s in
    if l = [] then term_of_preterm (retypecheck [] ptm) else
    failwith "Unparsed input following term" in
  preparse_ntrie,parse_ntrie;;

install_parser("ntrie",preparse_ntrie);;

(* ========================================================================= *)
(* Third part: Rules and conversions.                                        *)
(* ========================================================================= *)


module Ntrie_conversions = struct

(* ------------------------------------------------------------------------- *)
(* Basic definitions, handy tools and other preliminaries.                   *)
(* ------------------------------------------------------------------------- *)

let Comb(NUMERAL_tm,(Comb(BIT0_tm,Comb(BIT1_tm,zero_tm)))) =
  lhand(concl TWO)
let comb_numeral tm = mk_comb(NUMERAL_tm,tm)
let mk_bit0 tm = if tm = zero_tm then tm else mk_comb(BIT0_tm,tm)
and mk_bit1 tm = mk_comb(BIT1_tm,tm)
and ntrie_ty = type_of NEMPTY_tm

let neg_tm = `(~)`
and eq_tm = `(=):(num->bool)->(num->bool)->bool`
and iff_tm = `(=):bool->bool->bool`
and conj_tm = `(/\):bool->bool->bool`
and IN_tm = `(IN):num->(num->bool)->bool`
and EMPTY_tm = `{}:num->bool`
and SUBSET_tm = `(SUBSET):(num->bool)->(num->bool)->bool`
and PSUBSET_tm = `(PSUBSET):(num->bool)->(num->bool)->bool`
and DISJOINT_tm = `(DISJOINT):(num->bool)->(num->bool)->bool`
and INSERT_tm = `(INSERT):num->(num->bool)->(num->bool)`
and UNION_tm = `(UNION):(num->bool)->(num->bool)->(num->bool)`
and INTER_tm = `(INTER):(num->bool)->(num->bool)->(num->bool)`
and DELETE_tm = `(DELETE):(num->bool)->num->(num->bool)`
and DIFF_tm = `(DIFF):(num->bool)->(num->bool)->(num->bool)`

let [svar;svar1;svar2;tvar;tvar1;tvar2] =
  map (fun s -> mk_var(s,ntrie_ty)) ["s";"s1";"s2";"t";"t1";"t2"]
and nvar = `n:num`

let STANDARDIZE =
  let ilist =
    map (fun x -> x,x)
    [NEMPTY_tm; NZERO_tm; NNODE_tm; NTRIE_tm; IN_tm; eq_tm; SUBSET_tm;
     PSUBSET_tm; DISJOINT_tm; INSERT_tm; UNION_tm; INTER_tm; DELETE_tm;
     DIFF_tm; neg_tm; iff_tm; conj_tm; BIT0_tm; BIT1_tm; zero_tm;
     nvar; svar; svar1; svar2; tvar; tvar1; tvar2] in
  let rec replace tm =
    match tm with
      Var(_,_) | Const(_,_) -> rev_assocd tm ilist tm
    | Comb(s,t) -> mk_comb(replace s,replace t)
    | Abs(_,_) -> failwith "replace" in
  fun th -> let tm' = replace (concl th) in EQ_MP (REFL tm') th

(* ------------------------------------------------------------------------- *)
(* Well-formed (and minimal) ntries.                                         *)
(* ------------------------------------------------------------------------- *)

let wellformed =
  let rec visit =
    function
      Const("NEMPTY",_) -> ()
    | Const("NZERO",_) -> ()
    | Comb(Comb(Const("NNODE",_),stm),ttm) ->
        ( match stm,ttm with
            Const("NEMPTY",_),Const("NEMPTY",_) |
            Const("NZERO",_),Const("NEMPTY",_) -> fail()
          | _ -> visit stm; visit ttm )
    | _ -> fail() in
  function
    Comb(Const("NTRIE",_),tm) -> can visit tm
  | _ -> false

(* ------------------------------------------------------------------------- *)
(* Membership.                                                               *)
(* ------------------------------------------------------------------------- *)

let NUM_NZ_RULE,NTRIE_ZERO_IN_RULE,NTRIE_CHOOSE_RULE,NTRIE_IN_CONV =
  let rec NUM_NZ_RULE =
    let pth1,pth2 = (CONJ_PAIR o STANDARDIZE o prove)
     (`~(BIT1 n = _0) /\
       (~(n = _0) <=> ~(BIT0 n = _0))`,
      REWRITE_TAC[ARITH_EQ]) in
    function
      Comb(Const("BIT1",_),ntm) -> INST [ntm,nvar] pth1
    | Comb(Const("BIT0",_),ntm) ->
        let rth = NUM_NZ_RULE ntm
        and pth = INST [ntm,nvar] pth2 in
        EQ_MP pth rth
    | _ -> failwith "NUM_NZ_RULE" in
  let [zine_nth;zinx_pth;ine_nth;zinn_pth;pth4;pth5;pth6;pth7] =
    (CONJUNCTS o STANDARDIZE o prove)
    (`~(_0 IN NEMPTY) /\
      _0 IN NZERO /\
      ~(n IN NEMPTY) /\
      (_0 IN s <=> _0 IN NNODE s t) /\
      (n IN s <=> BIT0 n IN NNODE s t) /\
      (n IN t <=> BIT1 n IN NNODE s t) /\
      ~(BIT1 n IN NZERO) /\
      (~(n = _0) <=> ~(BIT0 n IN NZERO))`,
     REWRITE_TAC[NTRIE_IN; ARITH_EQ]) in
  let [zinn_nth;npth4;npth5] =
    map (AP_TERM neg_tm) [zinn_pth;pth4;pth5] in
  let rec NTRIE_ZERO_IN_RULE : term -> bool * thm =
    function
      Const("NEMPTY",_) -> false,zine_nth
    | Const("NZERO",_) -> true,zinx_pth
    | Comb(Comb(Const("NNODE",_),stm),ttm) ->
        let b,rth = NTRIE_ZERO_IN_RULE stm in
        let pth = if b then zinn_pth else zinn_nth in
        b,EQ_MP (INST [stm,svar; ttm,tvar] pth) rth
    | _ -> failwith "Malformed ntrie" in
  let rec NTRIE_CHOOSE_RULE =
    function
      Const("NEMPTY",_) -> failwith "Empty ntrie"
    | Const("NZERO",_) -> zinx_pth
    | Comb(Comb(Const("NNODE",_),stm),ttm) ->
        ( try let rth = NTRIE_CHOOSE_RULE ttm in
              let ntm = lhand(concl rth) in
              let pth = INST [ntm,nvar; stm,svar; ttm,tvar] pth5 in
              EQ_MP pth rth
          with Failure _ ->
              let rth = NTRIE_CHOOSE_RULE stm in
              let ntm = lhand(concl rth) in
              let pth = INST [ntm,nvar; stm,svar; ttm,tvar] pth4 in
              EQ_MP pth rth )
    | _ -> failwith "Malformed ntrie" in
  let NTRIE_IN_CONV : conv =
    let rec NTRIE_IN_RULE : term * term -> bool * thm =
      function
        Const("_0",_),stm -> NTRIE_ZERO_IN_RULE stm
      | ntm,Const("NEMPTY",_) -> false,INST [ntm,nvar] ine_nth
      | Comb(Const("BIT1",_),ntm),Const("NZERO",_) ->
          false,INST [ntm,nvar] pth6
      | Comb(Const("BIT0",_),ntm),Const("NZERO",_) ->
          let rth = NUM_NZ_RULE ntm in
          false,EQ_MP (INST [ntm,nvar] pth7) rth
      | Comb(Const("BIT0",_),ntm),Comb(Comb(Const("NNODE",_),stm),ttm) ->
          let b,rth = NTRIE_IN_RULE(ntm,stm) in
          let pth = if b then pth4 else npth4 in
          let pth = INST [ntm,nvar; stm,svar; ttm,tvar] pth in
          b,EQ_MP pth rth
      | Comb(Const("BIT1",_),ntm),Comb(Comb(Const("NNODE",_),stm),ttm) ->
          let b,rth = NTRIE_IN_RULE(ntm,ttm) in
          let pth = if b then pth5 else npth5 in
          let pth = INST [ntm,nvar; stm,svar; ttm,tvar] pth in
          b,EQ_MP pth rth
      | _ -> failwith "NTRIE_IN_RULE" in
    let NTRIE_IN_CONV : conv =
      let pth1,pth2 = (CONJ_PAIR o STANDARDIZE o prove)
        (`(n IN s <=> (NUMERAL n IN NTRIE s <=> T)) /\
          (~(n IN s) <=> (NUMERAL n IN NTRIE s <=> F))`,
         REWRITE_TAC[NUMERAL;NTRIE]) in
      function
        Comb(Comb(Const("IN",_),Comb(Const("NUMERAL",_),ntm)),
             Comb(Const("NTRIE",_),stm)) ->
          let b,rth = NTRIE_IN_RULE(ntm,stm) in
          let pth = if b then pth1 else pth2 in
          EQ_MP (INST [ntm,nvar; stm,svar] pth) rth
      | _ -> failwith "NTRIE_IN_CONV" in
    NTRIE_IN_CONV in
  NUM_NZ_RULE,NTRIE_ZERO_IN_RULE,NTRIE_CHOOSE_RULE,NTRIE_IN_CONV

(* ------------------------------------------------------------------------- *)
(* Inclusion.                                                                *)
(* ------------------------------------------------------------------------- *)

let NTRIE_SUBSET_CONV : conv =
  let [sub_refl_pth; esube_pth; xsubx_pth; esubx_pth; esub_pth; xsube_nth;
       sube_nth; xsubn_pth; xsubn_nth; nsubx_pth; nsubx_nth1; nsubx_nth2;
       nsubn_pth; nsubn_nth1; nsubn_nth2] =
   (CONJUNCTS o STANDARDIZE o prove)
   (`s SUBSET s /\
     NEMPTY SUBSET NEMPTY /\
     NZERO SUBSET NZERO /\
     NEMPTY SUBSET NZERO /\
     NEMPTY SUBSET t /\
     ~(NZERO SUBSET NEMPTY) /\
     (n IN s ==> ~(s SUBSET NEMPTY)) /\
     (NZERO SUBSET s <=> NZERO SUBSET NNODE s t) /\
     (~(NZERO SUBSET s) <=> ~(NZERO SUBSET NNODE s t)) /\
     (s SUBSET NZERO <=> NNODE s NEMPTY SUBSET NZERO) /\
     (~(s SUBSET NZERO) <=> ~(NNODE s NEMPTY SUBSET NZERO)) /\
     (n IN t ==> ~(NNODE s t SUBSET NZERO)) /\
     (s1 SUBSET s2 /\ t1 SUBSET t2 <=> NNODE s1 t1 SUBSET NNODE s2 t2) /\
     (~(s1 SUBSET s2) ==> ~(NNODE s1 t1 SUBSET NNODE s2 t2)) /\
     (~(t1 SUBSET t2) ==> ~(NNODE s1 t1 SUBSET NNODE s2 t2))`,
    SIMP_TAC[NTRIE_SUBSET] THEN REWRITE_TAC[NEMPTY] THEN SET_TAC[]) in
  let rec NTRIE_NZERO_SUBSET_RULE =
    function
      Const("NEMPTY",_) -> false,xsube_nth
    | Const("NZERO",_) -> true,xsubx_pth
    | Comb(Comb(Const("NNODE",_),stm),ttm) ->
        let b,rth = NTRIE_NZERO_SUBSET_RULE stm in
        let pth = if b then xsubn_pth else xsubn_nth in
        b,EQ_MP (INST [stm,svar; ttm,tvar] pth) rth
    | _ -> failwith "Malformed ntrie" in
  let rec NTRIE_SUBSET_NZERO_RULE =
    function
      Const("NEMPTY",_) -> true,esubx_pth
    | Const("NZERO",_) -> true,xsubx_pth
    | Comb(Comb(Const("NNODE",_),stm),Const("NEMPTY",_)) ->
        let b,rth = NTRIE_SUBSET_NZERO_RULE stm in
        let pth = if b then nsubx_pth else nsubx_nth1 in
        b,EQ_MP (INST [stm,svar] pth) rth
    | Comb(Comb(Const("NNODE",_),stm),ttm) ->
        let rth = NTRIE_CHOOSE_RULE ttm in
        let ntm = lhand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar; ttm,tvar] nsubx_nth2 in
        false,MP pth rth
    | _ -> failwith "Malformed ntrie" in
  let rec NTRIE_SUBSET_RULE =
    function
      Const("NEMPTY",_),Const("NEMPTY",_) -> true,esube_pth
    | Const("NEMPTY",_),Const("NZERO",_) -> true,esubx_pth
    | Const("NEMPTY",_),ttm -> true,INST [ttm,tvar] esub_pth
    | stm,Const("NEMPTY",_) ->
        let rth = NTRIE_CHOOSE_RULE stm in
        let ntm = lhand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar] sube_nth in
        false,MP pth rth
    | Const("NZERO",_),ttm -> NTRIE_NZERO_SUBSET_RULE ttm
    | stm,Const("NZERO",_) -> NTRIE_SUBSET_NZERO_RULE stm
    | stm,ttm when stm = ttm -> true,INST [stm,svar] sub_refl_pth
    | Comb(Comb(Const("NNODE",_),stm1),ttm1),
      Comb(Comb(Const("NNODE",_),stm2),ttm2) ->
        let b1,rth1 = NTRIE_SUBSET_RULE (stm1,stm2) in
        let pinst = INST[stm1,svar1; stm2,svar2; ttm1,tvar1; ttm2,tvar2] in
        if not b1 then false,MP (pinst nsubn_nth1) rth1 else
        let b2,rth2 = NTRIE_SUBSET_RULE (ttm1,ttm2) in
        if not b2 then false,MP (pinst nsubn_nth2) rth2 else
        true,EQ_MP (pinst nsubn_pth) (CONJ rth1 rth2)
    | _ -> failwith "Malformed ntrie" in
  let NTRIE_SUBSET_CONV : conv =
    let pth_sub_eqt,pth_sub_eqf = (CONJ_PAIR o STANDARDIZE o prove)
     (`(s SUBSET t <=> (NTRIE s SUBSET NTRIE t <=> T)) /\
       (~(s SUBSET t) <=> (NTRIE s SUBSET NTRIE t <=> F))`,
      REWRITE_TAC[NTRIE]) in
    function
      Comb(Comb(Const("SUBSET",_),Comb(Const("NTRIE",_),stm)),
                Comb(Const("NTRIE",_),ttm)) ->
        let b,rth = NTRIE_SUBSET_RULE(stm,ttm) in
        let pth = if b then pth_sub_eqt else pth_sub_eqf in
        EQ_MP (INST [stm,svar; ttm,tvar] pth) rth
    | _ -> failwith "NTRIE_SUBSET_CONV" in
  NTRIE_SUBSET_CONV

(* ------------------------------------------------------------------------- *)
(* Equality.                                                                 *)
(* ------------------------------------------------------------------------- *)

let NTRIE_EQ_CONV : conv =
  let [eq_refl_pth;eeqe_pth;xeqx_pth;eeqx_nth;xeqe_nth;eqe_nth;eeq_nth;
       eqx_nth1;eqx_nth2;neqn_pth;neqn_nth1;neqn_nth2] =
   (CONJUNCTS o STANDARDIZE o prove)
   (`s = s /\
     NEMPTY = NEMPTY /\
     NZERO = NZERO /\
     ~(NEMPTY = NZERO) /\
     ~(NZERO = NEMPTY) /\
     (n IN s ==> ~(s = NEMPTY)) /\
     (n IN t ==> ~(NEMPTY = t)) /\
     (~(n = _0) ==> n IN s ==> ~(s = NZERO)) /\
     (~(n = _0) ==> n IN t ==> ~(NZERO = t)) /\
     (s1 = s2 /\ t1 = t2 <=> NNODE s1 t1 = NNODE s2 t2) /\
     (~(s1 = s2) ==> ~(NNODE s1 t1 = NNODE s2 t2)) /\
     (~(t1 = t2) ==> ~(NNODE s1 t1 = NNODE s2 t2))`,
    SIMP_TAC[NTRIE_EQ] THEN SET_TAC[NEMPTY; NZERO]) in
  let rec NTRIE_EQ_RULE =
    function
      Const("NEMPTY",_),Const("NEMPTY",_) -> true,eeqe_pth
    | Const("NZERO",_),Const("NZERO",_) -> true,xeqx_pth
    | Const("NEMPTY",_),Const("NZERO",_) -> false,eeqx_nth
    | Const("NZERO",_),Const("NEMPTY",_) -> false,xeqe_nth
    | stm,Const("NEMPTY",_) ->
        let rth = NTRIE_CHOOSE_RULE stm in
        let ntm = lhand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar] eqe_nth in
        false,MP pth rth
    | Const("NEMPTY",_),ttm ->
        let rth = NTRIE_CHOOSE_RULE ttm in
        let ntm = lhand(concl rth) in
        let pth = INST [ntm,nvar; ttm,tvar] eeq_nth in
        false,MP pth rth
    | stm,Const("NZERO",_) ->
        let rth = NTRIE_CHOOSE_RULE stm in
        let ntm = lhand(concl rth) in
        let zth = NUM_NZ_RULE ntm in
        let pth = INST [ntm,nvar; stm,svar] eqx_nth1 in
        false,MP (MP pth zth) rth
    | Const("NZERO",_),ttm ->
        let rth = NTRIE_CHOOSE_RULE ttm in
        let ntm = lhand(concl rth) in
        let zth = NUM_NZ_RULE ntm in
        let pth = INST [ntm,nvar; ttm,tvar] eqx_nth2 in
        false,MP (MP pth zth) rth
    | stm,ttm when stm = ttm -> true,INST [stm,svar] eq_refl_pth
    | Comb(Comb(Const("NNODE",_),stm1),ttm1),
      Comb(Comb(Const("NNODE",_),stm2),ttm2) ->
        let b1,rth1 = NTRIE_EQ_RULE(stm1,stm2) in
        let pinst = INST[stm1,svar1; stm2,svar2; ttm1,tvar1; ttm2,tvar2] in
        if not b1 then false,MP (pinst neqn_nth1) rth1 else
        let b2,rth2 = NTRIE_EQ_RULE(ttm1,ttm2) in
        if not b2 then false,MP (pinst neqn_nth2) rth2 else
        failwith "Malformed ntrie"
    | _ -> failwith "Malformed ntrie" in
  let pth1,pth2 = (CONJ_PAIR o STANDARDIZE o prove)
   (`(s = t <=> (NTRIE s = NTRIE t <=> T)) /\
     (~(s = t) <=> (NTRIE s = NTRIE t <=> F))`,
    REWRITE_TAC[NTRIE]) in
  function
    Comb(Comb(Const("=",_),Comb(Const("NTRIE",_),stm)),
              Comb(Const("NTRIE",_),ttm)) ->
      let b,rth = NTRIE_EQ_RULE(stm,ttm) in
      let pth = if b then pth1 else pth2 in
      EQ_MP (INST [stm,svar; ttm,tvar] pth) rth
  | _ -> failwith "NTRIE_SUBSET_CONV"

(* ------------------------------------------------------------------------- *)
(* Singleton.                                                                *)
(* ------------------------------------------------------------------------- *)

let NTRIE_SING_RULE,NTRIE_SING_CONV =
  let [pth0;pth1;pth2;pth3] = (CONJUNCTS o STANDARDIZE o prove)
   (`({n} = s <=> ({NUMERAL n} = NTRIE s)) /\
     ({_0} = NZERO) /\
     ({n} = s ==> {BIT0 n} = NNODE s NEMPTY) /\
     ({n} = s <=> {BIT1 n} = NNODE NEMPTY s)`,
    REWRITE_TAC[NTRIE_SING; NTRIE; NTRIE_EQ] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NTRIE_EQ] THEN MESON_TAC[NZERO]) in
  let rec NTRIE_SING_RULE =
    function
      Const("_0",_) -> pth1
    | Comb(Const("BIT0",_),ntm) ->
        let rth = NTRIE_SING_RULE ntm in
        let stm = rand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar] pth2 in
        MP pth rth
    | Comb(Const("BIT1",_),ntm) ->
        let rth = NTRIE_SING_RULE ntm in
        let stm = rand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar] pth3 in
        EQ_MP pth rth
    | _ -> failwith "Malformed numeral" in
  let NTRIE_SING_CONV : conv =
    function
      Comb(Comb(Const("INSERT",_),Comb(Const("NUMERAL",_),ntm)),
           Const("EMPTY",_)) ->
        let rth = NTRIE_SING_RULE ntm in
        let stm = rand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar] pth0 in
        EQ_MP pth rth
    | _ -> failwith "NTRIE_SING_CONV" in
  NTRIE_SING_RULE,NTRIE_SING_CONV

(* ------------------------------------------------------------------------- *)
(* Insertion.                                                                *)
(* ------------------------------------------------------------------------- *)

let NTRIE_INSERT_RULE,NTRIE_INSERT_CONV =
  let [pth0;pth1;pth2;pth3;pth4;pth5;pth6;pth7;pth8] =
   (CONJUNCTS o STANDARDIZE o prove)
   (`(n INSERT s = t <=> NUMERAL n INSERT NTRIE s = NTRIE t) /\
     ({n} = s <=> n INSERT NEMPTY = s) /\
     (_0 INSERT NEMPTY = NZERO) /\
     (_0 INSERT NZERO = NZERO) /\
     (_0 INSERT s = s1 <=> _0 INSERT NNODE s t = NNODE s1 t) /\
     (n INSERT NZERO = t <=> BIT0 n INSERT NZERO = NNODE t NEMPTY) /\
     ({n} = t <=> BIT1 n INSERT NZERO = NNODE NZERO t) /\
     (n INSERT s = s1 <=> BIT0 n INSERT NNODE s t = NNODE s1 t) /\
     (n INSERT t = t1 <=> BIT1 n INSERT NNODE s t = NNODE s t1)`,
    REWRITE_TAC[NTRIE_INSERT; NTRIE_EQ] THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NTRIE_INSERT; NTRIE_EQ] THEN
    MESON_TAC[NEMPTY; NZERO]) in
  let rec NTRIE_INSERT_RULE =
    function
      Const("_0",_),Const("NEMPTY",_) -> pth2
    | Const("_0",_),Const("NZERO",_) -> pth3
    | Const("_0",_),Comb(Comb(Const("NNODE",_),stm),ttm) ->
        let rth = NTRIE_INSERT_RULE(zero_tm,stm) in
        let stm1 = rand(concl rth) in
        let pth = INST [stm,svar; ttm,tvar; stm1,svar1] pth4 in
        EQ_MP pth rth
    | ntm,Const("NEMPTY",_) ->
        let rth = NTRIE_SING_RULE ntm in
        let stm = rand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar] pth1 in
        EQ_MP pth rth
    | Comb(Const("BIT0",_),ntm),Const("NZERO",_) ->
        let rth = NTRIE_INSERT_RULE(ntm,NZERO_tm) in
        let ttm = rand(concl rth) in
        let pth = INST [ntm,nvar; ttm,tvar] pth5 in
        EQ_MP pth rth
    | Comb(Const("BIT1",_),ntm),Const("NZERO",_) ->
        let rth = NTRIE_SING_RULE ntm in
        let ttm = rand(concl rth) in
        let pth = INST [ntm,nvar; ttm,tvar] pth6 in
        EQ_MP pth rth
    | Comb(Const("BIT0",_),ntm),
           Comb(Comb(Const("NNODE",_),stm),ttm) ->
        let rth = NTRIE_INSERT_RULE(ntm,stm) in
        let stm1 = rand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar; ttm,tvar; stm1,svar1] pth7 in
        EQ_MP pth rth
    | Comb(Const("BIT1",_),ntm),
           Comb(Comb(Const("NNODE",_),stm),ttm) ->
        let rth = NTRIE_INSERT_RULE(ntm,ttm) in
        let ttm1 = rand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar; ttm,tvar; ttm1,tvar1] pth8 in
        EQ_MP pth rth
    | _ -> failwith "Malformed ntrie or numeral" in
  let NTRIE_INSERT_CONV : conv =
    function
      Comb(Comb(Const("INSERT",_),Comb(Const("NUMERAL",_),ntm)),
           Comb(Const("NTRIE",_),stm)) ->
        let rth = NTRIE_INSERT_RULE(ntm,stm) in
        let ttm = rand(concl rth) in
        let pth = INST [ntm,nvar; stm,svar; ttm,tvar] pth0 in
        EQ_MP pth rth
    | _ -> failwith "NTRIE_INSERT_CONV" in
  NTRIE_INSERT_RULE,NTRIE_INSERT_CONV

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let NTRIE_UNION_CONV : conv =
  let [pth0;pth1;pth2;pth3;pth4;pth5;pth6;pth7;pth8;pth9] =
   (CONJUNCTS o STANDARDIZE o prove)
   (`(s1 UNION s2 = s <=> NTRIE s1 UNION NTRIE s2 = NTRIE s) /\
     NEMPTY UNION NEMPTY = NEMPTY /\
     NEMPTY UNION NZERO = NZERO /\
     NZERO UNION NEMPTY = NZERO /\
     NZERO UNION NZERO = NZERO /\
     (s UNION NEMPTY = s) /\
     (NEMPTY UNION t = t) /\
     (s UNION NZERO = s1 <=> NNODE s t UNION NZERO = NNODE s1 t) /\
     (s UNION NZERO = s1 <=> NZERO UNION NNODE s t = NNODE s1 t) /\
     (s1 UNION s2 = s /\ t1 UNION t2 = t <=>
      NNODE s1 t1 UNION NNODE s2 t2 = NNODE s t)`,
    REPEAT STRIP_TAC THEN TRY EQ_TAC THEN
    REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
    REWRITE_TAC[NTRIE_UNION; NTRIE; NTRIE_EQ]) in
  let rec NTRIE_UNION_NZERO =
    function
      Const("NEMPTY",_) -> pth2
    | Const("NZERO",_) -> pth4
    | Comb(Comb(Const("NNODE",_),stm),ttm) ->
        NTRIE_NNODE_UNION_NZERO (stm,ttm)
    | _ -> failwith "Malformed ntrie"
  and NTRIE_NNODE_UNION_NZERO (stm,ttm) =
    let rth = NTRIE_UNION_NZERO stm in
    let stm1 = rand(concl rth) in
    let pth = INST [stm,svar; stm1,svar1; ttm,tvar] pth7 in
    EQ_MP pth rth
  and NTRIE_NZERO_UNION_NNODE (stm,ttm) =
    let rth = NTRIE_UNION_NZERO stm in
    let stm1 = rand(concl rth) in
    let pth = INST [stm,svar; stm1,svar1; ttm,tvar] pth8 in
    EQ_MP pth rth in
  let rec NTRIE_UNION_RULE =
    function
      Const("NEMPTY",_),Const("NEMPTY",_) -> pth1
    | Const("NEMPTY",_),Const("NZERO",_) -> pth2
    | Const("NZERO",_),Const("NEMPTY",_) -> pth3
    | Const("NZERO",_),Const("NZERO",_) -> pth4
    | stm,Const("NEMPTY",_) -> INST [stm,svar] pth5
    | Const("NEMPTY",_),ttm -> INST [ttm,tvar] pth6
    | Comb(Comb(Const("NNODE",_),stm),ttm),Const("NZERO",_) ->
        NTRIE_NNODE_UNION_NZERO (stm,ttm)
    | Const("NZERO",_),Comb(Comb(Const("NNODE",_),stm),ttm) ->
        NTRIE_NZERO_UNION_NNODE (stm,ttm)
    | Comb(Comb(Const("NNODE",_),stm1),ttm1),
      Comb(Comb(Const("NNODE",_),stm2),ttm2) ->
        let rth1 = NTRIE_UNION_RULE(stm1,stm2)
        and rth2 = NTRIE_UNION_RULE(ttm1,ttm2) in
        let stm = rand(concl rth1)
        and ttm = rand(concl rth2) in
        let pth = INST [stm,svar; stm1,svar1; stm2,svar2;
                        ttm,tvar; ttm1,tvar1; ttm2,tvar2]
                       pth9 in
        EQ_MP pth (CONJ rth1 rth2)
    | _ -> failwith "Malformed ntrie" in
  let NTRIE_UNION_CONV : conv =
    function
      Comb(Comb(Const("UNION",_),Comb(Const("NTRIE",_),stm1)),
                Comb(Const("NTRIE",_),stm2)) ->
        let rth = NTRIE_UNION_RULE(stm1,stm2) in
        let stm = rand(concl rth) in
        EQ_MP (INST [stm,svar; stm1,svar1; stm2,svar2] pth0) rth
    | _ -> failwith "NTRIE_UNION_CONV" in
  NTRIE_UNION_CONV

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* ------------------------------------------------------------------------- *)

let MK_NNODE_RULE =
  let pth0,pth1 = (CONJ_PAIR o STANDARDIZE o prove)
   (`NNODE NEMPTY NEMPTY = NEMPTY  /\
     NNODE NZERO NEMPTY = NZERO`,
    REWRITE_TAC[NTRIE_EQ]) in
  function
    Const("NEMPTY",_),Const("NEMPTY",_) -> pth0
  | Const("NZERO",_),Const("NEMPTY",_) -> pth1
  | _ -> failwith "MK_NNODE_RULE"

let NTRIE_INTER_CONV : conv =
  let [pth0;pth1;pth2;pth3;pth4;pth5;pth6;pth7;pth8;pth9;npth9;pth10] =
   (CONJUNCTS o STANDARDIZE o prove)
   (`(s1 INTER s2 = s <=> NTRIE s1 INTER NTRIE s2 = NTRIE s) /\
     NEMPTY INTER NEMPTY = NEMPTY /\
     NEMPTY INTER NZERO = NEMPTY /\
     NZERO INTER NEMPTY = NEMPTY /\
     s INTER NEMPTY = NEMPTY /\
     NEMPTY INTER t = NEMPTY /\
     NZERO INTER NZERO = NZERO /\
     (s INTER NZERO = s1 <=> NNODE s t INTER NZERO = s1) /\
     (s INTER NZERO = s1 <=> NZERO INTER NNODE s t = s1) /\
     (_0 IN t <=> NZERO INTER t = NZERO) /\
     (~(_0 IN t) <=> NZERO INTER t = NEMPTY) /\
     (s1 INTER s2 = s /\ t1 INTER t2 = t <=>
      NNODE s1 t1 INTER NNODE s2 t2 = NNODE s t)`,
    REWRITE_TAC[NTRIE_INTER; NTRIE_EQ; NTRIE; NZERO; NEMPTY] THEN SET_TAC[]) in
  let rec NTRIE_INTER_NZERO =
    function
      Const("NEMPTY",_) -> pth2
    | Const("NZERO",_) -> pth6
    | Comb(Comb(Const("NNODE",_),stm),ttm) ->
        NTRIE_NNODE_INTER_NZERO (stm,ttm)
    | _ -> failwith "Malformed ntrie"
  and NTRIE_NNODE_INTER_NZERO (stm,ttm) =
    let rth = NTRIE_INTER_NZERO stm in
    let stm1 = rand(concl rth) in
    let pth = INST [stm,svar; stm1,svar1; ttm,tvar] pth7 in
    EQ_MP pth rth
  and NTRIE_NZERO_INTER_NNODE (stm,ttm) =
    let rth = NTRIE_INTER_NZERO stm in
    let stm1 = rand(concl rth) in
    let pth = INST [stm,svar; stm1,svar1; ttm,tvar] pth8 in
    EQ_MP pth rth in
  let rec NTRIE_INTER_RULE =
    function
      Const("NEMPTY",_),Const("NEMPTY",_) -> pth1
    | Const("NEMPTY",_),Const("NZERO",_) -> pth2
    | Const("NZERO",_),Const("NEMPTY",_) -> pth3
    | Const("NZERO",_),Const("NZERO",_) -> pth6
    | stm,Const("NEMPTY",_) -> INST [stm,svar] pth4
    | Const("NEMPTY",_),ttm -> INST [ttm,tvar] pth5
    | Comb(Comb(Const("NNODE",_),stm),ttm),Const("NZERO",_) ->
        NTRIE_NNODE_INTER_NZERO(stm,ttm)
    | Const("NZERO",_),Comb(Comb(Const("NNODE",_),stm),ttm) ->
        NTRIE_NZERO_INTER_NNODE(stm,ttm)
    | Const("NZERO",_),ttm ->
        let b,rth = NTRIE_ZERO_IN_RULE ttm in
        let pth = if b then pth9 else npth9 in
        EQ_MP (INST [ttm,tvar] pth) rth
    | Comb(Comb(Const("NNODE",_),stm1),ttm1),
      Comb(Comb(Const("NNODE",_),stm2),ttm2) ->
        let rth1 = NTRIE_INTER_RULE(stm1,stm2)
        and rth2 = NTRIE_INTER_RULE(ttm1,ttm2) in
        let stm = rand(concl rth1)
        and ttm = rand(concl rth2) in
        let pth = INST [stm,svar; stm1,svar1; stm2,svar2;
                        ttm,tvar; ttm1,tvar1; ttm2,tvar2]
                       pth10 in
        let th = EQ_MP pth (CONJ rth1 rth2) in
        ( try TRANS th (MK_NNODE_RULE(stm,ttm))
          with Failure _ -> th )
    | _ -> failwith "Malformed ntrie" in
  let NTRIE_INTER_CONV : conv =
    function
      Comb(Comb(Const("INTER",_),Comb(Const("NTRIE",_),stm1)),
                Comb(Const("NTRIE",_),stm2)) ->
        let rth = NTRIE_INTER_RULE(stm1,stm2) in
        let stm = rand(concl rth) in
        EQ_MP (INST [stm,svar; stm1,svar1; stm2,svar2] pth0) rth
    | _ -> failwith "NTRIE_INTER_CONV" in
  NTRIE_INTER_CONV

(* ------------------------------------------------------------------------- *)
(* Deletion.                                                                 *)
(* ------------------------------------------------------------------------- *)

let NTRIE_DELETE_ZERO,NTRIE_NNODE_DELETE_ZERO,NTRIE_DELETE_CONV =
  let [pth0;pth1;pth2;pth3;pth4;pth5;pth6;pth7;pth8] =
   (CONJUNCTS o STANDARDIZE o prove)
   (`(s DELETE n = t <=> NTRIE s DELETE NUMERAL n = NTRIE t) /\
     NEMPTY DELETE _0 = NEMPTY /\
     NEMPTY DELETE n = NEMPTY /\
     NZERO DELETE _0 = NEMPTY /\
     (~(n = _0) <=> NZERO DELETE BIT0 n = NZERO) /\
     NZERO DELETE BIT1 n = NZERO /\
     (s DELETE _0 = s1 <=> NNODE s t DELETE _0 = NNODE s1 t) /\
     (s DELETE n = s1 <=> NNODE s t DELETE BIT0 n = NNODE s1 t) /\
     (t DELETE n = t1 <=> NNODE s t DELETE BIT1 n = NNODE s t1)`,
     REWRITE_TAC[NTRIE_DELETE; ARITH_EQ; NTRIE] THEN
     MESON_TAC[NTRIE_EQ; NTRIE_DELETE]) in
  let rec NTRIE_DELETE_ZERO =
    function
      Const("NEMPTY",_) -> pth1
    | Const("NZERO",_) -> pth3
    | Comb(Comb(Const("NNODE",_),stm),ttm) ->
        NTRIE_NNODE_DELETE_ZERO(stm,ttm)
    | _ -> failwith "Malformed ntrie"
  and NTRIE_NNODE_DELETE_ZERO (stm,ttm) =
    let rth = NTRIE_DELETE_ZERO stm in
    let stm1 = rand(concl rth) in
    let pth = INST [stm,svar; stm1,svar1; ttm,tvar] pth6 in
    EQ_MP pth rth in
  let NTRIE_DELETE_CONV : conv =
    let rec NTRIE_DELETE_RULE =
      function
        Const("NEMPTY",_),Const("_0",_) -> pth1
      | Const("NEMPTY",_),ntm -> INST [ntm,nvar] pth2
      | Const("NZERO",_),Const("_0",_) -> pth3
      | Comb(Comb(Const("NNODE",_),stm),ttm),Const("_0",_) ->
          NTRIE_NNODE_DELETE_ZERO(stm,ttm)
      | Const("NZERO",_),Comb(Const("BIT0",_),ntm) ->
          let rth = NUM_NZ_RULE ntm in
          EQ_MP (INST [ntm,nvar] pth4) rth
      | Const("NZERO",_),Comb(Const("BIT1",_),ntm) -> INST [ntm,nvar] pth5
      | Comb(Comb(Const("NNODE",_),stm),ttm),Comb(Const("BIT0",_),ntm) ->
          let rth = NTRIE_DELETE_RULE(stm,ntm) in
          let stm1 = rand(concl rth) in
          let pth = INST [ntm,nvar; stm,svar; stm1,svar1; ttm,tvar] pth7 in
          let th = EQ_MP pth rth in
          ( try TRANS th (MK_NNODE_RULE(stm1,ttm)) with Failure _ -> th )
      | Comb(Comb(Const("NNODE",_),stm),ttm),Comb(Const("BIT1",_),ntm) ->
          let rth = NTRIE_DELETE_RULE(ttm,ntm) in
          let ttm1 = rand(concl rth) in
          let pth = INST [ntm,nvar; stm,svar; ttm,tvar; ttm1,tvar1] pth8 in
          let th = EQ_MP pth rth in
          ( try TRANS th (MK_NNODE_RULE(stm,ttm1)) with Failure _ -> th )
      | _ -> failwith "Malformed ntrie" in
    function
      Comb(Comb(Const("DELETE",_),Comb(Const("NTRIE",_),stm)),
                Comb(Const("NUMERAL",_),ntm)) ->
        let rth = NTRIE_DELETE_RULE(stm,ntm) in
        let ttm = rand(concl rth) in
        EQ_MP (INST [ntm,nvar; stm,svar; ttm,tvar] pth0) rth
    | _ -> failwith "NTRIE_DELETE_CONV" in
  NTRIE_DELETE_ZERO,NTRIE_NNODE_DELETE_ZERO,NTRIE_DELETE_CONV

(* ------------------------------------------------------------------------- *)
(* Disjointedness.                                                           *)
(* ------------------------------------------------------------------------- *)

let NTRIE_DISJOINT_CONV : conv =
  let [pth0;pth1;pth2;pth3;pth4;pth5;pth6;pth7;pth8;pth9;pth10;pth11;pth12] =
   (CONJUNCTS o STANDARDIZE o prove)
   (`DISJOINT NEMPTY NEMPTY /\
     DISJOINT NEMPTY NZERO /\
     DISJOINT NZERO NEMPTY /\
     ~DISJOINT NZERO NZERO /\
     DISJOINT s NEMPTY /\
     DISJOINT NEMPTY t /\
     (_0 IN s <=> ~DISJOINT s NZERO) /\
     (~(_0 IN s) <=> DISJOINT s NZERO) /\
     (_0 IN t <=> ~DISJOINT NZERO t) /\
     (~(_0 IN t) <=> DISJOINT NZERO t) /\
     (DISJOINT s1 s2 /\ DISJOINT t1 t2 <=>
     DISJOINT (NNODE s1 t1) (NNODE s2 t2)) /\
     (~DISJOINT s1 s2 ==> ~DISJOINT (NNODE s1 t1) (NNODE s2 t2)) /\
     (~DISJOINT t1 t2 ==> ~DISJOINT (NNODE s1 t1) (NNODE s2 t2))`,
    SIMP_TAC[NTRIE_DISJOINT] THEN REWRITE_TAC[NZERO] THEN SET_TAC[]) in
  let rec NTRIE_DISJOINT_RULE =
    function
      Const("NEMPTY",_),Const("NEMPTY",_) -> true,pth0
    | Const("NEMPTY",_),Const("NZERO",_) -> true,pth1
    | Const("NZERO",_),Const("NEMPTY",_) -> true,pth2
    | Const("NZERO",_),Const("NZERO",_) -> false,pth3
    | stm,Const("NEMPTY",_) -> true,INST [stm,svar] pth4
    | Const("NEMPTY",_),ttm -> true,INST [ttm,tvar] pth5
    | stm,Const("NZERO",_) ->
        let b,rth = NTRIE_ZERO_IN_RULE stm in
        let pinst = INST [stm,svar] in
        let pth = pinst (if b then pth6 else pth7) in
        not b,EQ_MP pth rth
    | Const("NZERO",_),ttm ->
        let b,rth = NTRIE_ZERO_IN_RULE ttm in
        let pinst = INST [ttm,tvar] in
        let pth = pinst (if b then pth8 else pth9) in
        not b,EQ_MP pth rth
    | Comb(Comb(Const("NNODE",_),stm1),ttm1),
      Comb(Comb(Const("NNODE",_),stm2),ttm2) ->
        let b1,rth1 = NTRIE_DISJOINT_RULE (stm1,stm2) in
        let pinst = INST [stm1,svar1; stm2,svar2; ttm1,tvar1; ttm2,tvar2] in
        if not b1 then false,MP (pinst pth11) rth1 else
        let b2,rth2 = NTRIE_DISJOINT_RULE (ttm1,ttm2) in
        if not b2 then false,MP (pinst pth12) rth2 else
        true,EQ_MP (pinst pth10) (CONJ rth1 rth2)
    | _ -> failwith "Malformed ntrie" in
  let pth1,pth2 = (CONJ_PAIR o STANDARDIZE o prove)
   (`(DISJOINT s t <=> (DISJOINT (NTRIE s) (NTRIE t) <=> T)) /\
     (~DISJOINT s t <=> (DISJOINT (NTRIE s) (NTRIE t) <=> F))`,
    REWRITE_TAC[NTRIE]) in
  function
    Comb(Comb(Const("DISJOINT",_),Comb(Const("NTRIE",_),stm)),
              Comb(Const("NTRIE",_),ttm)) ->
      let b,rth = NTRIE_DISJOINT_RULE(stm,ttm) in
      let pth = if b then pth1 else pth2 in
      EQ_MP (INST [stm,svar; ttm,tvar] pth) rth
  | _ -> failwith "NTRIE_DISJOINT_CONV"

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

let NTRIE_DIFF_CONV : conv =
  let [pth0;pth1;pth2;pth3;pth4;pth5;pth6;pth7;pth8;pth9] =
   (CONJUNCTS o STANDARDIZE o prove)
   (`NEMPTY DIFF NEMPTY = NEMPTY /\
     NEMPTY DIFF NZERO = NEMPTY /\
     NZERO DIFF NEMPTY = NZERO /\
     NZERO DIFF NZERO = NEMPTY /\
     NEMPTY DIFF t = NEMPTY /\
     s DIFF NEMPTY = s /\
     s DIFF NZERO = s DELETE _0 /\
     (_0 IN t <=> NZERO DIFF t = NEMPTY) /\
     (~(_0 IN t) <=> NZERO DIFF t = NZERO) /\
     (s1 DIFF s2 = s /\ t1 DIFF t2 = t <=>
      NNODE s1 t1 DIFF NNODE s2 t2 = NNODE s t)`,
    REWRITE_TAC[NTRIE_DIFF; NTRIE_EQ] THEN
    REWRITE_TAC[NZERO; NEMPTY] THEN SET_TAC[]) in
  let rec NTRIE_DIFF_RULE =
    function
      Const("NEMPTY",_),Const("NEMPTY",_) -> pth0
    | Const("NEMPTY",_),Const("NZERO",_) -> pth1
    | Const("NZERO",_),Const("NEMPTY",_) -> pth2
    | Const("NZERO",_),Const("NZERO",_) -> pth3
    | stm,Const("NEMPTY",_) -> INST [stm,svar] pth5
    | Const("NEMPTY",_),ttm -> INST [ttm,tvar] pth4
    | stm,Const("NZERO",_) ->
        let rth = NTRIE_DELETE_ZERO stm in
        let pth = INST [stm,svar] pth6 in
        TRANS pth rth
    | Const("NZERO",_),ttm ->
        let b,rth = NTRIE_ZERO_IN_RULE ttm in
        let pinst = INST [ttm,tvar] in
        let pth = pinst(if b then pth7 else pth8) in
        EQ_MP pth rth
    | Comb(Comb(Const("NNODE",_),stm1),ttm1),
      Comb(Comb(Const("NNODE",_),stm2),ttm2) ->
        let rth1 = NTRIE_DIFF_RULE(stm1,stm2)
        and rth2 = NTRIE_DIFF_RULE(ttm1,ttm2) in
        let stm = rand(concl rth1)
        and ttm = rand(concl rth2) in
        let pth = INST [stm,svar; stm1,svar1; stm2,svar2;
                        ttm,tvar; ttm1,tvar1; ttm2,tvar2]
                       pth9 in
        let th = EQ_MP pth (CONJ rth1 rth2) in
        ( try TRANS th (MK_NNODE_RULE(stm,ttm)) with Failure _ -> th )
    | _ -> failwith "Malformed ntrie" in
  let pth = (STANDARDIZE o prove)
   (`(s DIFF t = s1 <=> NTRIE s DIFF NTRIE t = NTRIE s1)`,
    REWRITE_TAC[NTRIE]) in
  function
    Comb(Comb(Const("DIFF",_),Comb(Const("NTRIE",_),stm)),
              Comb(Const("NTRIE",_),ttm)) ->
      let rth = NTRIE_DIFF_RULE(stm,ttm) in
      let rtm = rand(concl rth) in
      EQ_MP (INST [stm,svar; ttm,tvar; rtm,svar1] pth) rth
  | _ -> failwith "NTRIE_DIFF_CONV"

(* ------------------------------------------------------------------------- *)
(* Encoding from and decoding to set enumerations.                           *)
(* ------------------------------------------------------------------------- *)

let NTRIE_ENCODE_CONV : conv =
  let [pth0;pth1;pth2] = (CONJUNCTS o STANDARDIZE o prove)
   (`{} = NEMPTY /\
     s = NTRIE s /\
     (INSERT) (NUMERAL n) = (INSERT) n`,
    REWRITE_TAC[NTRIE; NEMPTY; NUMERAL]) in
  let rec NTRIE_ENC_CONV : conv =
    function
      Const("EMPTY",ty) when ty = ntrie_ty -> pth0
    | Comb(Comb(Const("INSERT",_),Comb(Const("NUMERAL",_),ntm)),stm) ->
        let rth1 = NTRIE_ENC_CONV stm in
        let ttm = rand(concl rth1) in
        let rth2 = MK_COMB ((INST [ntm,nvar] pth2),rth1) in
        TRANS rth2 (NTRIE_INSERT_RULE (ntm,ttm))
    | _ -> failwith "NTRIE_ENC_CONV" in
  fun tm ->
    let rth = NTRIE_ENC_CONV tm in
    let stm = rand(concl rth) in
    TRANS rth (INST [stm,svar] pth1);;

let NTRIE_DECODE_CONV : conv =
  fun tm ->
    let l = dest_small_ntrie tm in
    let tm' = mk_numset (map mk_small_numeral (sort (<) l)) in
    SYM (NTRIE_ENCODE_CONV tm');;

end

let NTRIE_IN_CONV : conv       = Ntrie_conversions.NTRIE_IN_CONV
and NTRIE_SUBSET_CONV : conv   = Ntrie_conversions.NTRIE_SUBSET_CONV
and NTRIE_EQ_CONV : conv       = Ntrie_conversions.NTRIE_EQ_CONV
and NTRIE_SING_CONV : conv     = Ntrie_conversions.NTRIE_SING_CONV
and NTRIE_INSERT_CONV : conv   = Ntrie_conversions.NTRIE_INSERT_CONV
and NTRIE_UNION_CONV : conv    = Ntrie_conversions.NTRIE_UNION_CONV
and NTRIE_INTER_CONV : conv    = Ntrie_conversions.NTRIE_INTER_CONV
and NTRIE_DELETE_CONV : conv   = Ntrie_conversions.NTRIE_DELETE_CONV
and NTRIE_DISJOINT_CONV : conv = Ntrie_conversions.NTRIE_DISJOINT_CONV
and NTRIE_DIFF_CONV : conv     = Ntrie_conversions.NTRIE_DIFF_CONV
and NTRIE_ENCODE_CONV : conv   = Ntrie_conversions.NTRIE_ENCODE_CONV
and NTRIE_DECODE_CONV : conv   = Ntrie_conversions.NTRIE_DECODE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Final hack-together.                                                      *)
(* ------------------------------------------------------------------------- *)

let NTRIE_REL_CONV : conv =
  let gconv_net = itlist (uncurry net_of_conv)
    [`NTRIE s = NTRIE t`, NTRIE_EQ_CONV;
     `NTRIE s SUBSET NTRIE t`, NTRIE_SUBSET_CONV;
     `DISJOINT (NTRIE s) (NTRIE t)`, NTRIE_DISJOINT_CONV;
     `NUMERAL n IN NTRIE s`, NTRIE_IN_CONV]
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let NTRIE_RED_CONV : conv =
  let gconv_net = itlist (uncurry net_of_conv)
    [`NTRIE s = NTRIE t`, NTRIE_EQ_CONV;
     `NTRIE s SUBSET NTRIE t`, NTRIE_SUBSET_CONV;
     `DISJOINT (NTRIE s) (NTRIE t)`, NTRIE_DISJOINT_CONV;
     `NUMERAL n IN NTRIE s`, NTRIE_IN_CONV;
     `NUMERAL n INSERT NTRIE s`, NTRIE_INSERT_CONV;
     `NTRIE s UNION NTRIE t`, NTRIE_UNION_CONV;
     `NTRIE s INTER NTRIE t`, NTRIE_INTER_CONV;
     `NTRIE s DELETE NUMERAL n`, NTRIE_DELETE_CONV;
     `NTRIE s DIFF NTRIE t`, NTRIE_DIFF_CONV]
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let NTRIE_REDUCE_CONV = DEPTH_CONV NTRIE_RED_CONV;;

let NTRIE_REDUCE_TAC = CONV_TAC NTRIE_REDUCE_CONV;;
