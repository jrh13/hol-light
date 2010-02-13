(* ========================================================================= *)
(* Computations with finite sets of nums.                                    *)
(*                                                                           *)
(*        (c) Copyright, Clelia Lomuto, Marco Maggesi, 2009.                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* This file defines some conversions that operate on finite sets of nums    *)
(* represented literally in a trie-like structure (we call them `ntries').   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Example:                                                                  *)
(* # NTRIE_COMPUTE NTRIE_REDUCE_CONV                                         *)
(*   `{10, 1001, 3} INTER {3, 7, 10} SUBSET {10, 10000} UNION {3, 33}`;;     *)
(* val it : thm =                                                            *)
(* |- {10, 1001, 3} INTER {3, 7, 10} SUBSET {10, 10000} UNION {3, 33} <=> T  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Constructors for the ntrie representation of a set of nums.               *)
(* ------------------------------------------------------------------------- *)

let NEMPTY = new_definition
  `NEMPTY:num->bool = {}`;;

let NZERO = new_definition
  `NZERO = {_0}`;;

let NNODE = new_definition
  `!s t. NNODE s t = IMAGE BIT0 s UNION IMAGE BIT1 t`;;

let NTRIE = new_definition
  `!s:num->bool. NTRIE s = s`;;

let NTRIE_RELATIONS = prove
  (`NNODE NEMPTY NEMPTY = NEMPTY /\
    NNODE NZERO NEMPTY = NZERO`,
   REWRITE_TAC[NEMPTY; NZERO; NNODE; EXTENSION; NOT_IN_EMPTY;
               IN_INSERT; IN_UNION; IN_IMAGE] THEN
   MESON_TAC[ARITH_EQ]);;

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
   REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE; NOT_IN_EMPTY; IN_INSERT;
               IN_UNION; IN_IMAGE; ARITH_EQ] THEN
   MESON_TAC[]);;

let NTRIE_IN_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_IN in
  REWR_CONV tth THENC REWRITE_CONV[pths; CONJUNCT2 ARITH_EQ];;

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
   REWRITE_TAC[NTRIE; NEMPTY; NZERO; NNODE; EMPTY_SUBSET; SUBSET_REFL;
               SING_SUBSET; NOT_IN_EMPTY] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[SUBSET; NOT_IN_EMPTY; IN_INSERT; IN_UNION; IN_IMAGE;
               ARITH_EQ] THENL
   [MESON_TAC[]; MESON_TAC[ARITH_EQ]; MESON_TAC[]; EQ_TAC] THENL
   [ALL_TAC; MESON_TAC[ARITH_EQ]] THEN
   STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THENL
   [POP_ASSUM (MP_TAC o SPEC `BIT0 x`);
    POP_ASSUM (MP_TAC o SPEC `BIT1 x`)] THEN
   REWRITE_TAC[ARITH_EQ] THEN MESON_TAC[]);;

let NTRIE_SUBSET_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_SUBSET in
  REWR_CONV tth THENC REWRITE_CONV[pths];;

(* ------------------------------------------------------------------------- *)
(* Equality.                                                                 *)
(* ------------------------------------------------------------------------- *)

let NTRIE_EQ = prove
  (`(!s t. NTRIE s = NTRIE t <=> s = t) /\
    (!s:num->bool. s = s) /\
    ~(NZERO = NEMPTY) /\
    ~(NEMPTY = NZERO) /\
    (!s t. NNODE s t = NEMPTY <=> s = NEMPTY /\ t = NEMPTY) /\
    (!s t. NEMPTY = NNODE s t <=> s = NEMPTY /\ t = NEMPTY) /\
    (!s t. NNODE s t = NZERO <=> s = NZERO /\ t = NEMPTY) /\
    (!s t. NZERO = NNODE s t <=> s = NZERO /\ t = NEMPTY) /\
    (!s1 s2 t1 t2. NNODE s1 t1 = NNODE s2 t2 <=> s1 = s2 /\ t1 = t2)`,
   REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; NTRIE_SUBSET; NEMPTY; NZERO] THEN
   SET_TAC[]);;

let NTRIE_EQ_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_EQ in
  REWR_CONV tth THENC REWRITE_CONV[pths];;

(* ------------------------------------------------------------------------- *)
(* Singleton.                                                                *)
(* ------------------------------------------------------------------------- *)

let NTRIE_SING = prove
  (`(!n. {NUMERAL n} = NTRIE {n}) /\
    {_0} = NZERO /\
    (!n. {BIT0 n} = if n = _0 then NZERO else NNODE {n} NEMPTY) /\
    (!n. {BIT1 n} = NNODE NEMPTY {n})`,
   REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE; IMAGE_CLAUSES;
               UNION_EMPTY] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_ZERO]);;

let NTRIE_SING_CONV =
  let tth,pths = CONJ_PAIR NTRIE_SING in
  REWR_CONV tth THENC RAND_CONV(REWRITE_CONV[pths; CONJUNCT2 ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Insertion.                                                                *)
(* ------------------------------------------------------------------------- *)

let NTRIE_INSERT = prove
  (`(!s n. NUMERAL n INSERT NTRIE s = NTRIE (n INSERT s)) /\
    (!n. n INSERT NEMPTY = {n}) /\
    _0 INSERT NZERO = NZERO /\
    (!s t n. _0 INSERT NNODE s t = NNODE (_0 INSERT s) t) /\
    (!n. BIT0 n INSERT NZERO = if n = _0 then NZERO else
                               NNODE (n INSERT NZERO) NEMPTY) /\
    (!n. BIT1 n INSERT NZERO = NNODE NZERO {n}) /\
    (!s t n. BIT0 n INSERT NNODE s t = NNODE (n INSERT s) t) /\
    (!s t n. BIT1 n INSERT NNODE s t = NNODE s (n INSERT t))`,
   REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE] THEN
   REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
   REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_UNION; IN_IMAGE] THEN
   ASM_MESON_TAC[ARITH_EQ]);;

let NTRIE_INSERT_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_INSERT in
  REWR_CONV tth THENC
  RAND_CONV(REWRITE_CONV[pths; CONJUNCT2 NTRIE_SING; CONJUNCT2 ARITH_EQ]);;

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
   REWRITE_TAC[NTRIE; NEMPTY; NZERO; NNODE] THEN REPEAT STRIP_TAC THEN
   TRY COND_CASES_TAC THEN
   REWRITE_TAC[UNION_EMPTY; INSERT_UNION; NOT_IN_EMPTY; IN_INSERT; IN_UNION;
               IN_IMAGE; EXTENSION] THEN
   MESON_TAC[ARITH_EQ]);;

let NTRIE_UNION_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_UNION in
  REWR_CONV tth THENC RAND_CONV(REWRITE_CONV[pths]);;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* Warning: rewriting with this theorem generates ntries which are not       *)
(* "minimal".  It has to be used in conjuction with NTRIE_RELATIONS.         *)
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
   REWRITE_TAC[NTRIE; NEMPTY; NZERO; NNODE; INTER_EMPTY; INSERT_INTER;
               NOT_IN_EMPTY; IN_INSERT] THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_IMAGE; ARITH_EQ] THEN ASM_MESON_TAC[];
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE;
                    IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[ARITH_EQ];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_IMAGE] THEN
    MESON_TAC[ARITH_EQ]]);;

let NTRIE_INTER_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_INTER in
  REWR_CONV tth THENC RAND_CONV(REWRITE_CONV[pths; NTRIE_RELATIONS]);;

(* ------------------------------------------------------------------------- *)
(* Deleting an element.                                                      *)
(* Warning: rewriting with this theorem generates ntries which are not       *)
(* "minimal".  It has to be used in conjuction with NTRIE_RELATIONS.         *)
(* ------------------------------------------------------------------------- *)

let NTRIE_DELETE = prove
  (`(!s n. NTRIE s DELETE NUMERAL n = NTRIE (s DELETE n)) /\
    (!n. NEMPTY DELETE n = NEMPTY) /\
    (!n. NZERO DELETE n = if n = _0 then NEMPTY else NZERO) /\
    (!s t. NNODE s t DELETE _0 = NNODE (s DELETE _0) t) /\
    (!s t n. NNODE s t DELETE BIT0 n = NNODE (s DELETE n) t) /\
    (!s t n. NNODE s t DELETE BIT1 n = NNODE s (t DELETE n))`,
   REWRITE_TAC[NUMERAL; NTRIE; NEMPTY; NZERO; NNODE] THEN REPEAT STRIP_TAC THEN
   TRY COND_CASES_TAC THEN
   ASM_REWRITE_TAC[EXTENSION; IN_DELETE; IN_UNION; IN_IMAGE;
                   NOT_IN_EMPTY; IN_INSERT] THEN
   ASM_MESON_TAC[ARITH_EQ]);;

let NTRIE_DELETE_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_DELETE in
  REWR_CONV tth THENC RAND_CONV(REWRITE_CONV[pths; NTRIE_RELATIONS]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint.                                                                 *)
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

let NTRIE_DISJOINT_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_DISJOINT in
  REWR_CONV tth THENC REWRITE_CONV[pths];;

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
   REWRITE_TAC[NTRIE; NEMPTY; NZERO; NNODE; EMPTY_DIFF; DIFF_EMPTY;
               DIFF_EQ_EMPTY; EXTENSION; NOT_IN_EMPTY; IN_INSERT; IN_DIFF;
               IN_UNION; IN_IMAGE] THEN
   MESON_TAC[ARITH_EQ]);;

let NTRIE_DIFF_CONV : conv =
  let tth,pths = CONJ_PAIR NTRIE_DIFF in
  REWR_CONV tth THENC REWRITE_CONV[pths];;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

let NTRIE_IMAGE_DEF = new_definition
  `!f acc s. NTRIE_IMAGE f acc s = IMAGE f s UNION acc`;;

let NTRIE_IMAGE = prove
  (`(!f acc. NTRIE_IMAGE f acc NEMPTY = acc) /\
    (!f acc. NTRIE_IMAGE f acc NZERO = f _0 INSERT acc) /\
    (!f acc s t. NTRIE_IMAGE f acc (NNODE s t) =
                 NTRIE_IMAGE (\n. f (BIT1 n))
                             (NTRIE_IMAGE (\n. f (BIT0 n)) acc s)
                             t)`,
   REWRITE_TAC[NEMPTY; NZERO; NNODE; NTRIE_IMAGE_DEF; GSYM IMAGE_o; o_DEF;
               IMAGE_UNION; IMAGE_CLAUSES; UNION_EMPTY; INSERT_UNION] THEN
   REPEAT STRIP_TAC THENL [COND_CASES_TAC THEN ASM SET_TAC[]; SET_TAC[]]);;

let IMAGE_EQ_NTRIE_IMAGE = prove
  (`!f s. IMAGE f (NTRIE s) = NTRIE_IMAGE (\n. f (NUMERAL n)) {} s`,
   REWRITE_TAC [NUMERAL; NTRIE; ETA_AX; NTRIE_IMAGE_DEF; UNION_EMPTY]);;

let NTRIE_IMAGE_CONV : conv -> conv =
  let [c1;c2;c3] = map REWR_CONV (CONJUNCTS NTRIE_IMAGE) in
  fun cnv ->
  let rec conv tm =
    (c1 ORELSEC (c2 THENC LAND_CONV (TRY_CONV BETA_CONV THENC cnv)) ORELSEC
     (c3 THENC
      RATOR_CONV (ONCE_DEPTH_CONV BETA_CONV THENC RAND_CONV conv) THENC
      conv)) tm in
  REWR_CONV IMAGE_EQ_NTRIE_IMAGE THENC (ONCE_DEPTH_CONV BETA_CONV) THENC conv;;

(* ------------------------------------------------------------------------- *)
(* Decoding of a set in ntrie form to the usual literal representation.      *)
(* ------------------------------------------------------------------------- *)

let NTRIE_DECODE_CONV : conv =
  let NTRIE_DECODE_THM = prove
    (`!s. NTRIE s = NTRIE_IMAGE NUMERAL {} s`,
     REWRITE_TAC[NTRIE; NUMERAL; NTRIE_IMAGE_DEF; UNION_EMPTY; IMAGE] THEN
     SET_TAC[])
  and [c1;c2;c3] = map REWR_CONV (CONJUNCTS NTRIE_IMAGE) in
  let rec conv tm =
    (c1 ORELSEC (c2 THENC LAND_CONV (TRY_CONV BETA_CONV)) ORELSEC
     (c3 THENC
      RATOR_CONV (ONCE_DEPTH_CONV BETA_CONV THENC RAND_CONV conv) THENC
      conv)) tm in
  REWR_CONV NTRIE_DECODE_THM THENC conv;;

(* ------------------------------------------------------------------------- *)
(* Encoding of a set from the usual literal form to the ntrie form.          *)
(* ------------------------------------------------------------------------- *)

let NTRIE_ENCODE_CONV : conv=
  let itm = `(INSERT):num->(num->bool)->num->bool`
  and th = prove (`{} = NTRIE NEMPTY`, REWRITE_TAC[NTRIE; NEMPTY]) in
  let cnv1 = REWR_CONV th
  and cnv2 cnv tm =
    let fn,arg = dest_comb tm in
    if rator fn <> itm then fail () else
    AP_TERM fn (cnv arg) in
  let rec conv tm = (cnv1 ORELSEC (cnv2 conv THENC NTRIE_INSERT_CONV)) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Final hack-together.                                                      *)
(* ------------------------------------------------------------------------- *)

let NTRIE_REL_CONV : conv =
  let gconv_net = itlist (uncurry net_of_conv)
    [`NTRIE s = NTRIE t`, NTRIE_EQ_CONV;
     `NTRIE s SUBSET NTRIE t`, NTRIE_SUBSET_CONV;
     `DISJOINT (NTRIE s) (NTRIE t)`, NTRIE_DISJOINT_CONV;
     `NUMERA n IN NTRIE s`, NTRIE_IN_CONV]
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let NTRIE_RED_CONV : conv =
  let gconv_net = itlist (uncurry net_of_conv)
    [`NTRIE s = NTRIE t`, NTRIE_EQ_CONV;
     `NTRIE s SUBSET NTRIE t`, NTRIE_SUBSET_CONV;
     `DISJOINT (NTRIE s) (NTRIE t)`, NTRIE_DISJOINT_CONV;
     `NUMERA n IN NTRIE s`, NTRIE_IN_CONV;
     `NUMERAL n INSERT NTRIE s`, NTRIE_INSERT_CONV;
     `NTRIE s UNION NTRIE t`, NTRIE_UNION_CONV;
     `NTRIE s INTER NTRIE t`, NTRIE_INTER_CONV;
     `NTRIE s DELETE NUMERAL n`, NTRIE_DELETE_CONV;
     `NTRIE s DIFF NTRIE t`, NTRIE_DIFF_CONV]
    (basic_net()) in
  REWRITES_CONV gconv_net;;

let NTRIE_REDUCE_CONV = DEPTH_CONV NTRIE_RED_CONV;;

let NTRIE_REDUCE_TAC = CONV_TAC NTRIE_REDUCE_CONV;;

let NTRIE_COMPUTE (cnv : conv) : conv =
  ONCE_DEPTH_CONV NTRIE_ENCODE_CONV THENC
  cnv THENC
  ONCE_DEPTH_CONV NTRIE_DECODE_CONV;;
