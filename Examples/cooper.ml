(* ========================================================================= *)
(* Implementation of Cooper's algorithm via proforma theorems.               *)
(* ========================================================================= *)

prioritize_int();;

(* ------------------------------------------------------------------------- *)
(* Basic syntax on integer terms.                                            *)
(* ------------------------------------------------------------------------- *)

let dest_mul = dest_binop `(*)`;;
let dest_add = dest_binop `(+)`;;

(* ------------------------------------------------------------------------- *)
(* Divisibility.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("divides",(12,"right"));;

let divides = new_definition
  `a divides b <=> ?x. b = a * x`;;

(* ------------------------------------------------------------------------- *)
(* Trivial lemmas about integers.                                            *)
(* ------------------------------------------------------------------------- *)

let INT_DOWN2 = prove
 (`!a b. ?c. !x. x < c ==> x < a /\ x < b`,
  MESON_TAC[INT_LE_TOTAL; INT_LET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Trivial lemmas about divisibility.                                        *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_ADD = prove
 (`!d a b. d divides a /\ d divides b ==> d divides (a + b)`,
  MESON_TAC[divides; INT_ADD_LDISTRIB]);;

let DIVIDES_SUB = prove
 (`!d a b. d divides a /\ d divides b ==> d divides (a - b)`,
  MESON_TAC[divides; INT_SUB_LDISTRIB]);;

let DIVIDES_ADD_REVR = prove
 (`!d a b. d divides a /\ d divides (a + b) ==> d divides b`,
  MESON_TAC[DIVIDES_SUB; INT_ARITH `(a + b) - a = b`]);;

let DIVIDES_ADD_REVL = prove
 (`!d a b. d divides b /\ d divides (a + b) ==> d divides a`,
  MESON_TAC[DIVIDES_SUB; INT_ARITH `(a + b) - b = a`]);;

let DIVIDES_LMUL = prove
 (`!d a x. d divides a ==> d divides (x * a)`,
  ASM_MESON_TAC[divides; INT_ARITH `a * b * c = b * a * c`]);;

let DIVIDES_RNEG = prove
 (`!d a. d divides (--a) <=> d divides a`,
  REWRITE_TAC[divides] THEN MESON_TAC[INT_MUL_RNEG; INT_NEG_NEG]);;

let DIVIDES_LNEG = prove
 (`!d a. (--d) divides a <=> d divides a`,
  REWRITE_TAC[divides] THEN
  MESON_TAC[INT_MUL_RNEG; INT_MUL_LNEG; INT_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* More specialized lemmas (see footnotes on p4 and p5).                     *)
(* ------------------------------------------------------------------------- *)

let INT_DOWN_MUL_LT = prove
 (`!x y d. &0 < d ==> ?c. x + c * d < y`,
  MESON_TAC[INT_ARCH; INT_LT_REFL;
            INT_ARITH `x - y < c * d <=> x + --c * d < y`]);;

let INT_MOD_LEMMA = prove
 (`!d x. &0 < d ==> ?c. &1 <= x + c * d /\ x + c * d <= d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:int`; `&0`] o MATCH_MP INT_DOWN_MUL_LT) THEN
  DISCH_THEN(X_CHOOSE_TAC `c0:int`) THEN
  SUBGOAL_THEN `?c1. &0 <= c1 /\ --(x + c0 * d) < c1 * d` MP_TAC THENL
   [SUBGOAL_THEN `?c1. --(x + c0 * d) < c1 * d` MP_TAC THENL
     [ASM_MESON_TAC[INT_ARCH; INT_ARITH `&0 < d ==> ~(d = &0)`]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
      `(&0 < --c1 ==> &0 < --cd) /\ xcod < &0
       ==> --xcod < cd ==> &0 <= c1`) THEN
    ASM_SIMP_TAC[GSYM INT_MUL_LNEG; INT_LT_MUL]; ALL_TAC] THEN
  REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`; GSYM NOT_FORALL_THM] THEN
  REWRITE_TAC[GSYM INT_FORALL_POS] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  REWRITE_TAC[INT_ARITH `--(x + a * d) < b * d <=> &1 <= x + (a + b) * d`] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c0 + &n` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  UNDISCH_TAC `&1 <= x + (c0 + &n) * d` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`] THENL
   [REWRITE_TAC[SUB_0; LT_REFL; INT_ADD_RID] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN INT_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_SUC; LT] THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Shadow for restricted class of formulas.                                  *)
(* ------------------------------------------------------------------------- *)

let cform_INDUCT,cform_RECURSION = define_type
  "cform = Lt int
         | Gt int
         | Eq int
         | Ne int
         | Divides int int
         | Ndivides int int
         | And cform cform
         | Or cform cform
         | Nox bool";;

(* ------------------------------------------------------------------------- *)
(* Interpretation of a cform.                                                *)
(* ------------------------------------------------------------------------- *)

let interp = new_recursive_definition cform_RECURSION
  `(interp x (Lt e) <=> x + e < &0) /\
   (interp x (Gt e) <=> x + e > &0) /\
   (interp x (Eq e) <=> (x + e = &0)) /\
   (interp x (Ne e) <=> ~(x + e = &0)) /\
   (interp x (Divides c e) <=> c divides (x + e)) /\
   (interp x (Ndivides c e) <=> ~(c divides (x + e))) /\
   (interp x (And p q) <=> interp x p /\ interp x q) /\
   (interp x (Or p q) <=> interp x p \/ interp x q) /\
   (interp x (Nox P) <=> P)`;;

(* ------------------------------------------------------------------------- *)
(* The "minus infinity" and "plus infinity" variants.                        *)
(* ------------------------------------------------------------------------- *)

let minusinf = new_recursive_definition cform_RECURSION
 `(minusinf (Lt e) = Nox T) /\
  (minusinf (Gt e) = Nox F) /\
  (minusinf (Eq e) = Nox F) /\
  (minusinf (Ne e) = Nox T) /\
  (minusinf (Divides c e) = Divides c e) /\
  (minusinf (Ndivides c e) = Ndivides c e) /\
  (minusinf (And p q) = And (minusinf p) (minusinf q)) /\
  (minusinf (Or p q) = Or (minusinf p) (minusinf q)) /\
  (minusinf (Nox P) = Nox P)`;;

let plusinf = new_recursive_definition cform_RECURSION
 `(plusinf (Lt e) = Nox F) /\
  (plusinf (Gt e) = Nox T) /\
  (plusinf (Eq e) = Nox F) /\
  (plusinf (Ne e) = Nox T) /\
  (plusinf (Divides c e) = Divides c e) /\
  (plusinf (Ndivides c e) = Ndivides c e) /\
  (plusinf (And p q) = And (plusinf p) (plusinf q)) /\
  (plusinf (Or p q) = Or (plusinf p) (plusinf q)) /\
  (plusinf (Nox P) = Nox P)`;;

(* ------------------------------------------------------------------------- *)
(* All the "dividing" things divide the given constant (e.g. their LCM).     *)
(* ------------------------------------------------------------------------- *)

let alldivide = new_recursive_definition cform_RECURSION
 `(alldivide d (Lt e) <=> T) /\
  (alldivide d (Gt e) <=> T) /\
  (alldivide d (Eq e) <=> T) /\
  (alldivide d (Ne e) <=> T) /\
  (alldivide d (Divides c e) <=> c divides d) /\
  (alldivide d (Ndivides c e) <=> c divides d) /\
  (alldivide d (And p q) <=> alldivide d p /\ alldivide d q) /\
  (alldivide d (Or p q) <=> alldivide d p /\ alldivide d q) /\
  (alldivide d (Nox P) <=> T)`;;

(* ------------------------------------------------------------------------- *)
(* A-sets and B-sets.                                                        *)
(* ------------------------------------------------------------------------- *)

let aset = new_recursive_definition cform_RECURSION
 `(aset (Lt e) = {(--e)}) /\
  (aset (Gt e) = {}) /\
  (aset (Eq e) = {(--e + &1)}) /\
  (aset (Ne e) = {(--e)}) /\
  (aset (Divides c e) = {}) /\
  (aset (Ndivides c e) = {}) /\
  (aset (And p q) = (aset p) UNION (aset q)) /\
  (aset (Or p q) = (aset p) UNION (aset q)) /\
  (aset (Nox P) = {})`;;

let bset = new_recursive_definition cform_RECURSION
 `(bset (Lt e) = {}) /\
  (bset (Gt e) = {(--e)}) /\
  (bset (Eq e) = {(--(e + &1))}) /\
  (bset (Ne e) = {(--e)}) /\
  (bset (Divides c e) = {}) /\
  (bset (Ndivides c e) = {}) /\
  (bset (And p q) = (bset p) UNION (bset q)) /\
  (bset (Or p q) = (bset p) UNION (bset q)) /\
  (bset (Nox P) = {})`;;

(* ------------------------------------------------------------------------- *)
(* The key minimality case analysis for the integers.                        *)
(* ------------------------------------------------------------------------- *)

let INT_EXISTS_CASES = prove
 (`(?x. P x) <=> (!y. ?x. x < y /\ P x) \/ (?x. P x /\ !y. y < x ==> ~P y)`,
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:int`) THEN
  MATCH_MP_TAC(TAUT `(~b ==> a) ==> a \/ b`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`; NOT_FORALL_THM;
              NOT_IMP] THEN
  STRIP_TAC THEN X_GEN_TAC `y:int` THEN
  DISJ_CASES_TAC(INT_ARITH `x < y \/ &0 <= x - y`) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ?y. y < x - &n /\ P y` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[INT_FORALL_POS] THEN
    DISCH_THEN(MP_TAC o SPEC `x - y`) THEN
    ASM_REWRITE_TAC[INT_ARITH `x - (x - y) = y`]] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[INT_SUB_RZERO; GSYM INT_OF_NUM_SUC] THEN
  ASM_MESON_TAC[INT_ARITH `z < y /\ y < x - &n ==> z < x - (&n + &1)`]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas towards the main theorems (following my book).                     *)
(* ------------------------------------------------------------------------- *)

let MINUSINF_LEMMA = prove
 (`!p. ?y. !x. x < y ==> (interp x p <=> interp x (minusinf p))`,
  MATCH_MP_TAC cform_INDUCT THEN
  REWRITE_TAC[interp; minusinf] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c /\ d) /\ (e /\ f) ==> a /\ b /\ c /\ d /\ e /\ f`) THEN
  CONJ_TAC THENL
   [MESON_TAC[INT_ARITH `x < --a ==> x + a < &0`; INT_GT;
              INT_LT_ANTISYM; INT_LT_REFL];
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM;
     RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`] INT_DOWN2) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[]);;

let MINUSINF_REPEATS = prove
 (`!p c d x. alldivide d p
             ==> (interp x (minusinf p) <=> interp (x + c * d) (minusinf p))`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN MATCH_MP_TAC cform_INDUCT THEN
  SIMP_TAC[interp; minusinf; alldivide] THEN
  ONCE_REWRITE_TAC[INT_ARITH `(x + d) + y = (x + y) + d`] THEN
  MESON_TAC[DIVIDES_LMUL; DIVIDES_ADD_REVL; DIVIDES_ADD]);;

let NOMINIMAL_EQUIV = prove
 (`alldivide d p /\ &0 < d
   ==> ((!y. ?x. x < y /\ interp x p) <=>
        ?j. &1 <= j /\ j <= d /\ interp j (minusinf p))`,
  ASM_MESON_TAC[MINUSINF_LEMMA; MINUSINF_REPEATS; INT_DOWN_MUL_LT;
                INT_DOWN2; INT_MOD_LEMMA]);;

let BDISJ_REPEATS_LEMMA = prove
 (`!d p. alldivide d p /\ &0 < d
         ==> !x. interp x p /\ ~(interp (x - d) p)
                 ==> ?j b. &1 <= j /\ j <= d /\ b IN bset p /\ (x = b + j)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> b ==> a ==> c`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC cform_INDUCT THEN
  REWRITE_TAC[interp; alldivide; bset; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC(TAUT `(a /\ b /\ c /\ d /\ e /\ f) /\ g /\ h
                     ==> a /\ b /\ c /\ d /\ e /\ f /\ g /\ h`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[TAUT `~a \/ a`;
             TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`;
             TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`;
             TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`;
             DE_MORGAN_THM; IN_UNION; EXISTS_OR_THM; FORALL_AND_THM]] THEN
  REPEAT STRIP_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`x + a`; `--a`];
    MAP_EVERY EXISTS_TAC [`&1`; `--a - &1`];
    MAP_EVERY EXISTS_TAC [`d:int`; `--a`];
    ASM_MESON_TAC[INT_ARITH `(x - y) + z = (x + z) - y`; DIVIDES_SUB];
    ASM_MESON_TAC[INT_ARITH `(x - y) + z = (x + z) - y`;
                  INT_ARITH `(x - y) + y = x`; DIVIDES_ADD]] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[IN_SING] THEN INT_ARITH_TAC);;

let MAINTHM_B = prove
 (`!p d. alldivide d p /\ &0 < d
         ==> ((?x. interp x p) <=>
              ?j. &1 <= j /\ j <= d /\
                  (interp j (minusinf p) \/
                   ?b. b IN bset p /\ interp (b + j) p))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`; EXISTS_OR_THM] THEN
  MATCH_MP_TAC(TAUT
   `!a1 a2. (a <=> a1 \/ a2) /\ (a1 <=> b) /\ (a2 ==> c) /\ (c ==> a)
            ==> (a <=> b \/ c)`) THEN
  EXISTS_TAC `!y. ?x. x < y /\ interp x p` THEN
  EXISTS_TAC `?x. interp x p /\ !y. y < x ==> ~(interp y p)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_EXISTS_CASES];
    ASM_MESON_TAC[NOMINIMAL_EQUIV];
    ALL_TAC;
    MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:int`
   (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x - d`))) THEN
  ASM_SIMP_TAC[INT_ARITH `&0 < d ==> x - d < x`] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`d:int`; `p:cform`] BDISJ_REPEATS_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:int`) THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Deduce the other one by a symmetry argument rather than a similar proof.  *)
(* ------------------------------------------------------------------------- *)

let mirror = new_recursive_definition cform_RECURSION
 `(mirror (Lt e) = Gt(--e)) /\
  (mirror (Gt e) = Lt(--e)) /\
  (mirror (Eq e) = Eq(--e)) /\
  (mirror (Ne e) = Ne(--e)) /\
  (mirror (Divides c e) = Divides c (--e)) /\
  (mirror (Ndivides c e) = Ndivides c (--e)) /\
  (mirror (And p q) = And (mirror p) (mirror q)) /\
  (mirror (Or p q) = Or (mirror p) (mirror q)) /\
  (mirror (Nox P) = Nox P)`;;

let INTERP_MIRROR_LEMMA = prove
 (`!p x. interp (--x) (mirror p) <=> interp x p`,
  MATCH_MP_TAC cform_INDUCT THEN SIMP_TAC[mirror; interp] THEN
  REWRITE_TAC[GSYM INT_NEG_ADD; DIVIDES_RNEG] THEN INT_ARITH_TAC);;

let INTERP_MIRROR = prove
 (`!p x. interp x (mirror p) <=> interp (--x) p`,
  MESON_TAC[INTERP_MIRROR_LEMMA; INT_NEG_NEG]);;

let BSET_MIRROR = prove
 (`!p. bset(mirror p) = IMAGE (--) (aset p)`,
  MATCH_MP_TAC cform_INDUCT THEN SIMP_TAC[mirror; aset; bset] THEN
  REWRITE_TAC[IMAGE_CLAUSES; IMAGE_UNION] THEN
  REWRITE_TAC[EXTENSION; IN_SING] THEN INT_ARITH_TAC);;

let MINUSINF_MIRROR = prove
 (`!p. minusinf (mirror p) = mirror (plusinf p)`,
  MATCH_MP_TAC cform_INDUCT THEN SIMP_TAC[plusinf; minusinf; mirror]);;

let PLUSINF_MIRROR = prove
 (`!p. plusinf p = mirror(minusinf (mirror p))`,
  MATCH_MP_TAC cform_INDUCT THEN
  SIMP_TAC[plusinf; minusinf; mirror; INT_NEG_NEG]);;

let ALLDIVIDE_MIRROR = prove
 (`!p d. alldivide d (mirror p) = alldivide d p`,
  MATCH_MP_TAC cform_INDUCT THEN SIMP_TAC[mirror; alldivide]);;

let EXISTS_NEG = prove
 (`(?x. P(--x)) <=> (?x. P(x))`,
  MESON_TAC[INT_NEG_NEG]);;

let FORALL_NEG = prove
 (`(!x. P(--x)) <=> (!x. P x)`,
  MESON_TAC[INT_NEG_NEG]);;

let EXISTS_MOD_IMP = prove
 (`!P d. (!c x. P(x + c * d) <=> P(x)) /\ (?j. &1 <= j /\ j <= d /\ P(--j))
         ==> ?j. &1 <= j /\ j <= d /\ P(j)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d:int = j` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`--(&2)`; `d:int`]) THEN
    ASM_REWRITE_TAC[INT_ARITH `d + --(&2) * d = --d`] THEN
    ASM_MESON_TAC[INT_LE_REFL];
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `--j`]) THEN
    ASM_REWRITE_TAC[INT_ARITH `--j + &1 * d = d - j`] THEN
    DISCH_TAC THEN EXISTS_TAC `d - j` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= j`; `j <= d`; `~(d:int = j)`] THEN
    INT_ARITH_TAC]);;

let EXISTS_MOD_EQ = prove
 (`!P d. (!c x. P(x + c * d) <=> P(x))
         ==> ((?j. &1 <= j /\ j <= d /\ P(--j)) <=>
              (?j. &1 <= j /\ j <= d /\ P(j)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MP_TAC(SPEC `P:int->bool` EXISTS_MOD_IMP);
    MP_TAC(SPEC `\x. P(--x):bool` EXISTS_MOD_IMP)] THEN
  DISCH_THEN(MP_TAC o SPEC `d:int`) THEN ASM_REWRITE_TAC[INT_NEG_NEG] THEN
  ASM_REWRITE_TAC[INT_ARITH `--(x + c * d) = --x + --c * d`; FORALL_NEG] THEN
  MESON_TAC[]);;

let MAINTHM_A = prove
 (`!p d. alldivide d p /\ &0 < d
         ==> ((?x. interp x p) <=>
              ?j. &1 <= j /\ j <= d /\
                  (interp j (plusinf p) \/
                   ?a. a IN aset p /\ interp (a - j) p))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM EXISTS_NEG] THEN
  REWRITE_TAC[GSYM INTERP_MIRROR] THEN
  MP_TAC(SPECL [`mirror p`; `d:int`] MAINTHM_B) THEN
  ASM_REWRITE_TAC[ALLDIVIDE_MIRROR] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`;
              TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`; EXISTS_OR_THM] THEN
  BINOP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[INTERP_MIRROR; MINUSINF_MIRROR; BSET_MIRROR] THEN
    REWRITE_TAC[INT_ARITH `--(b + j) = --b - j`; IN_IMAGE] THEN
    MESON_TAC[INT_NEG_NEG]] THEN
  REWRITE_TAC[PLUSINF_MIRROR] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALLDIVIDE_MIRROR]) THEN
  SPEC_TAC(`mirror p`,`q:cform`) THEN REWRITE_TAC[INTERP_MIRROR] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM EXISTS_MOD_EQ) THEN
  ASM_SIMP_TAC[GSYM MINUSINF_REPEATS]);;

(* ------------------------------------------------------------------------- *)
(* Proforma for elimination of coefficient of main variable.                 *)
(* ------------------------------------------------------------------------- *)

let EXISTS_MULTIPLE_THM_1 = prove
 (`(?x. P(&1 * x)) <=> ?x. P(x)`,
  REWRITE_TAC[INT_MUL_LID]);;

let EXISTS_MULTIPLE_THM = prove
 (`(?x. P(c * x)) <=> ?x. c divides x /\ P(x)`,
  MESON_TAC[divides]);;

(* ------------------------------------------------------------------------- *)
(* Ordering of variables determined by a list, *with* trivial default.       *)
(* ------------------------------------------------------------------------- *)

let rec earlier vars x y =
  match vars with
    z::ovs -> if z = y then false
              else if z = x then true
              else earlier ovs x y
  | [] -> x < y;;

(* ------------------------------------------------------------------------- *)
(* Conversion of integer constant to ML rational number.                     *)
(* This is a tweaked copy of the real-type versions in "real.ml".            *)
(* ------------------------------------------------------------------------- *)

let is_num_const =
  let ptm = `&` in
  fun tm -> try let l,r = dest_comb tm in
                l = ptm & is_numeral r
            with Failure _ -> false;;

let mk_num_const,dest_num_const =
  let ptm = `&` in
  (fun n -> mk_comb(ptm,mk_numeral n)),
  (fun tm -> let l,r = dest_comb tm in
             if l = ptm then dest_numeral r
             else failwith "dest_num_const");;

let is_int_const =
  let ptm = `(--)` in
  fun tm ->
    is_num_const tm or
    try let l,r = dest_comb tm in
        l = ptm & is_num_const r
    with Failure _ -> false;;

let mk_int_const,dest_int_const =
  let ptm = `(--)` in
  (fun n -> if n </ Int 0 then mk_comb(ptm,mk_num_const(minus_num n))
            else mk_num_const n),
  (fun tm -> if try rator tm = ptm with Failure _ -> false then
               minus_num (dest_num_const(rand tm))
             else dest_num_const tm);;

(* ------------------------------------------------------------------------- *)
(* Similar tweaks of all the REAL_INT_..._CONV arith convs in real.ml        *)
(* ------------------------------------------------------------------------- *)

let INT_LE_CONV,INT_LT_CONV,
    INT_GE_CONV,INT_GT_CONV,INT_EQ_CONV =
  let tth =
    TAUT `(F /\ F <=> F) /\ (F /\ T <=> F) /\
          (T /\ F <=> F) /\ (T /\ T <=> T)` in
  let nth = TAUT `(~T <=> F) /\ (~F <=> T)` in
  let NUM2_EQ_CONV =
    COMB2_CONV (RAND_CONV NUM_EQ_CONV) NUM_EQ_CONV THENC
    GEN_REWRITE_CONV I [tth] in
  let NUM2_NE_CONV =
    RAND_CONV NUM2_EQ_CONV THENC
    GEN_REWRITE_CONV I [nth] in
  let [pth_le1; pth_le2a; pth_le2b; pth_le3] = (CONJUNCTS o prove)
   (`(--(&m) <= &n <=> T) /\
     (&m <= &n <=> m <= n) /\
     (--(&m) <= --(&n) <=> n <= m) /\
     (&m <= --(&n) <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[INT_LE_NEG2] THEN
    REWRITE_TAC[INT_LE_LNEG; INT_LE_RNEG] THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LE; LE_0] THEN
    REWRITE_TAC[LE; ADD_EQ_0]) in
  let INT_LE_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_le1];
    GEN_REWRITE_CONV I [pth_le2a; pth_le2b] THENC NUM_LE_CONV;
    GEN_REWRITE_CONV I [pth_le3] THENC NUM2_EQ_CONV] in
  let [pth_lt1; pth_lt2a; pth_lt2b; pth_lt3] = (CONJUNCTS o prove)
   (`(&m < --(&n) <=> F) /\
     (&m < &n <=> m < n) /\
     (--(&m) < --(&n) <=> n < m) /\
     (--(&m) < &n <=> ~((m = 0) /\ (n = 0)))`,
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3;
                GSYM NOT_LE; GSYM INT_NOT_LE] THEN
    CONV_TAC TAUT) in
  let INT_LT_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_lt1];
    GEN_REWRITE_CONV I [pth_lt2a; pth_lt2b] THENC NUM_LT_CONV;
    GEN_REWRITE_CONV I [pth_lt3] THENC NUM2_NE_CONV] in
  let [pth_ge1; pth_ge2a; pth_ge2b; pth_ge3] = (CONJUNCTS o prove)
   (`(&m >= --(&n) <=> T) /\
     (&m >= &n <=> n <= m) /\
     (--(&m) >= --(&n) <=> m <= n) /\
     (--(&m) >= &n <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; INT_GE] THEN
    CONV_TAC TAUT) in
  let INT_GE_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_ge1];
    GEN_REWRITE_CONV I [pth_ge2a; pth_ge2b] THENC NUM_LE_CONV;
    GEN_REWRITE_CONV I [pth_ge3] THENC NUM2_EQ_CONV] in
  let [pth_gt1; pth_gt2a; pth_gt2b; pth_gt3] = (CONJUNCTS o prove)
   (`(--(&m) > &n <=> F) /\
     (&m > &n <=> n < m) /\
     (--(&m) > --(&n) <=> m < n) /\
     (&m > --(&n) <=> ~((m = 0) /\ (n = 0)))`,
    REWRITE_TAC[pth_lt1; pth_lt2a; pth_lt2b; pth_lt3; INT_GT] THEN
    CONV_TAC TAUT) in
  let INT_GT_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_gt1];
    GEN_REWRITE_CONV I [pth_gt2a; pth_gt2b] THENC NUM_LT_CONV;
    GEN_REWRITE_CONV I [pth_gt3] THENC NUM2_NE_CONV] in
  let [pth_eq1a; pth_eq1b; pth_eq2a; pth_eq2b] = (CONJUNCTS o prove)
   (`((&m = &n) <=> (m = n)) /\
     ((--(&m) = --(&n)) <=> (m = n)) /\
     ((--(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
     ((&m = --(&n)) <=> (m = 0) /\ (n = 0))`,
    REWRITE_TAC[GSYM INT_LE_ANTISYM; GSYM LE_ANTISYM] THEN
    REWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; LE; LE_0] THEN
    CONV_TAC TAUT) in
  let INT_EQ_CONV = FIRST_CONV
   [GEN_REWRITE_CONV I [pth_eq1a; pth_eq1b] THENC NUM_EQ_CONV;
    GEN_REWRITE_CONV I [pth_eq2a; pth_eq2b] THENC NUM2_EQ_CONV] in
  INT_LE_CONV,INT_LT_CONV,
  INT_GE_CONV,INT_GT_CONV,INT_EQ_CONV;;

let INT_NEG_CONV =
  let pth = prove
   (`(--(&0) = &0) /\
     (--(--(&x)) = &x)`,
    REWRITE_TAC[INT_NEG_NEG; INT_NEG_0]) in
  GEN_REWRITE_CONV I [pth];;

let INT_MUL_CONV =
  let pth0 = prove
   (`(&0 * &x = &0) /\
     (&0 * --(&x) = &0) /\
     (&x * &0 = &0) /\
     (--(&x) * &0 = &0)`,
    REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO])
  and pth1,pth2 = (CONJ_PAIR o prove)
   (`((&m * &n = &(m * n)) /\
      (--(&m) * --(&n) = &(m * n))) /\
     ((--(&m) * &n = --(&(m * n))) /\
      (&m * --(&n) = --(&(m * n))))`,
    REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG] THEN
    REWRITE_TAC[INT_OF_NUM_MUL]) in
  FIRST_CONV
   [GEN_REWRITE_CONV I [pth0];
    GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_MULT_CONV;
    GEN_REWRITE_CONV I [pth2] THENC RAND_CONV(RAND_CONV NUM_MULT_CONV)];;

let INT_ADD_CONV =
  let neg_tm = `(--)` in
  let amp_tm = `&` in
  let add_tm = `(+)` in
  let dest = dest_binop `(+)` in
  let m_tm = `m:num` and n_tm = `n:num` in
  let pth0 = prove
   (`(--(&m) + &m = &0) /\
     (&m + --(&m) = &0)`,
    REWRITE_TAC[INT_ADD_LINV; INT_ADD_RINV]) in
  let [pth1; pth2; pth3; pth4; pth5; pth6] = (CONJUNCTS o prove)
   (`(--(&m) + --(&n) = --(&(m + n))) /\
     (--(&m) + &(m + n) = &n) /\
     (--(&(m + n)) + &m = --(&n)) /\
     (&(m + n) + --(&m) = &n) /\
     (&m + --(&(m + n)) = --(&n)) /\
     (&m + &n = &(m + n))`,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_NEG_ADD] THEN
    REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID] THEN
    REWRITE_TAC[INT_ADD_RINV; INT_ADD_LID] THEN
    ONCE_REWRITE_TAC[INT_ADD_SYM] THEN
    REWRITE_TAC[INT_ADD_ASSOC; INT_ADD_LINV; INT_ADD_LID] THEN
    REWRITE_TAC[INT_ADD_RINV; INT_ADD_LID]) in
  GEN_REWRITE_CONV I [pth0] ORELSEC
  (fun tm ->
    try let l,r = dest tm in
        if rator l = neg_tm then
          if rator r = neg_tm then
            let th1 = INST [rand(rand l),m_tm; rand(rand r),n_tm] pth1 in
            let tm1 = rand(rand(rand(concl th1))) in
            let th2 = AP_TERM neg_tm (AP_TERM amp_tm (NUM_ADD_CONV tm1)) in
            TRANS th1 th2
          else
            let m = rand(rand l) and n = rand r in
            let m' = dest_numeral m and n' = dest_numeral n in
            if m' <=/ n' then
              let p = mk_numeral (n' -/ m') in
              let th1 = INST [m,m_tm; p,n_tm] pth2 in
              let th2 = NUM_ADD_CONV (rand(rand(lhand(concl th1)))) in
              let th3 = AP_TERM (rator tm) (AP_TERM amp_tm (SYM th2)) in
              TRANS th3 th1
            else
              let p = mk_numeral (m' -/ n') in
              let th1 = INST [n,m_tm; p,n_tm] pth3 in
              let th2 = NUM_ADD_CONV (rand(rand(lhand(lhand(concl th1))))) in
              let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2)) in
              let th4 = AP_THM (AP_TERM add_tm th3) (rand tm) in
              TRANS th4 th1
        else
          if rator r = neg_tm then
            let m = rand l and n = rand(rand r) in
            let m' = dest_numeral m and n' = dest_numeral n in
            if n' <=/ m' then
              let p = mk_numeral (m' -/ n') in
              let th1 = INST [n,m_tm; p,n_tm] pth4 in
              let th2 = NUM_ADD_CONV (rand(lhand(lhand(concl th1)))) in
              let th3 = AP_TERM add_tm (AP_TERM amp_tm (SYM th2)) in
              let th4 = AP_THM th3 (rand tm) in
              TRANS th4 th1
            else
             let p = mk_numeral (n' -/ m') in
             let th1 = INST [m,m_tm; p,n_tm] pth5 in
             let th2 = NUM_ADD_CONV (rand(rand(rand(lhand(concl th1))))) in
             let th3 = AP_TERM neg_tm (AP_TERM amp_tm (SYM th2)) in
             let th4 = AP_TERM (rator tm) th3 in
             TRANS th4 th1
          else
            let th1 = INST [rand l,m_tm; rand r,n_tm] pth6 in
            let tm1 = rand(rand(concl th1)) in
            let th2 = AP_TERM amp_tm (NUM_ADD_CONV tm1) in
            TRANS th1 th2
    with Failure _ -> failwith "INT_ADD_CONV");;

let INT_SUB_CONV =
  GEN_REWRITE_CONV I [INT_SUB] THENC
  TRY_CONV(RAND_CONV INT_NEG_CONV) THENC
  INT_ADD_CONV;;

let INT_POW_CONV =
  let n = `n:num` and x = `x:num` in
  let pth1,pth2 = (CONJ_PAIR o prove)
   (`(&x pow n = &(x EXP n)) /\
     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))`,
    REWRITE_TAC[INT_OF_NUM_POW; INT_POW_NEG]) in
  let tth = prove
   (`((if T then x:int else y) = x) /\ ((if F then x:int else y) = y)`,
    REWRITE_TAC[]) in
  let neg_tm = `(--)` in
  (GEN_REWRITE_CONV I [pth1] THENC RAND_CONV NUM_EXP_CONV) ORELSEC
  (GEN_REWRITE_CONV I [pth2] THENC
   RATOR_CONV(RATOR_CONV(RAND_CONV NUM_EVEN_CONV)) THENC
   GEN_REWRITE_CONV I [tth] THENC
   (fun tm -> if rator tm = neg_tm then RAND_CONV(RAND_CONV NUM_EXP_CONV) tm
              else RAND_CONV NUM_EXP_CONV  tm));;

(* ------------------------------------------------------------------------- *)
(* Handy utility functions for int arithmetic terms.                         *)
(* ------------------------------------------------------------------------- *)

let dest_add = dest_binop `(+)`;;
let dest_mul = dest_binop `(*)`;;
let dest_pow = dest_binop `(pow)`;;
let dest_sub = dest_binop `(-)`;;

let is_add = is_binop `(+)`;;
let is_mul = is_binop `(*)`;;
let is_pow = is_binop `(pow)`;;
let is_sub = is_binop `(-)`;;

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer.                                               *)
(* ------------------------------------------------------------------------- *)

let POLYNOMIAL_NORMALIZERS =
  let sth = prove
   (`(!x y z. x + (y + z) = (x + y) + z) /\
     (!x y. x + y = y + x) /\
     (!x. &0 + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z) /\
     (!x y. x * y = y * x) /\
     (!x. &1 * x = x) /\
     (!x. &0 * x = &0) /\
     (!x y z. x * (y + z) = x * y + x * z) /\
     (!x. x pow 0 = &1) /\
     (!x n. x pow (SUC n) = x * x pow n)`,
    REWRITE_TAC[INT_POW] THEN INT_ARITH_TAC)
  and rth = prove
   (`(!x. --x = --(&1) * x) /\
     (!x y. x - y = x + --(&1) * y)`,
    INT_ARITH_TAC)
  and is_semiring_constant = is_int_const
  and SEMIRING_ADD_CONV = INT_ADD_CONV
  and SEMIRING_MUL_CONV = INT_MUL_CONV
  and SEMIRING_POW_CONV = INT_POW_CONV in
  let NORMALIZERS =
   SEMIRING_NORMALIZERS_CONV sth rth
    (is_semiring_constant,
     SEMIRING_ADD_CONV,SEMIRING_MUL_CONV,SEMIRING_POW_CONV) in
  fun vars -> NORMALIZERS(earlier vars);;

let POLYNOMIAL_NEG_CONV vars =
  let cnv,_,_,_,_,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;

let POLYNOMIAL_ADD_CONV vars =
  let _,cnv,_,_,_,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;

let POLYNOMIAL_SUB_CONV vars =
  let _,_,cnv,_,_,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;

let POLYNOMIAL_MUL_CONV vars =
  let _,_,_,cnv,_,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;

let POLYNOMIAL_POW_CONV vars =
  let _,_,_,_,cnv,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;

let POLYNOMIAL_CONV vars =
  let _,_,_,_,_,cnv = POLYNOMIAL_NORMALIZERS vars in cnv;;

(* ------------------------------------------------------------------------- *)
(* Slight variants of these functions for procedure below.                   *)
(* ------------------------------------------------------------------------- *)

let LINEAR_CMUL =
  let mul_tm = `(*)` in
  fun vars n tm ->
    POLYNOMIAL_MUL_CONV vars (mk_comb(mk_comb(mul_tm,mk_int_const n),tm));;

(* ------------------------------------------------------------------------- *)
(* Linearize a formula, dealing with non-strict inequalities.                *)
(* ------------------------------------------------------------------------- *)

let LINEARIZE_CONV =
  let rew_conv = GEN_REWRITE_CONV I
    [CONJ (REFL `c divides e`)
          (INT_ARITH
              `(s < t <=> &0 < t - s) /\
               (~(s < t) <=> &0 < (s + &1) - t) /\
               (s > t <=> &0 < s - t) /\
               (~(s > t) <=> &0 < (t + &1) - s) /\
               (s <= t <=> &0 < (t + &1) - s) /\
               (~(s <= t) <=> &0 < s - t) /\
               (s >= t <=> &0 < (s + &1) - t) /\
               (~(s >= t) <=> &0 < t - s) /\
               ((s = t) <=> (&0 = s - t))`)]
  and true_tm = `T` and false_tm = `F` in
  let rec conv vars tm =
    try (rew_conv THENC RAND_CONV(POLYNOMIAL_CONV vars)) tm with Failure _ ->
    if is_exists tm or is_forall tm then
      let x = bndvar(rand tm) in BINDER_CONV (conv (x::vars)) tm
    else if is_neg tm then
      RAND_CONV (conv vars) tm
    else if is_conj tm or is_disj tm or is_imp tm or is_iff tm then
      BINOP_CONV (conv vars) tm
    else if tm = true_tm or tm = false_tm then REFL tm
    else failwith "LINEARIZE_CONV: Unexpected term type" in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Get the coefficient of x, assumed to be first term, if there at all.      *)
(* ------------------------------------------------------------------------- *)

let coefficient x tm =
  try let l,r = dest_add tm in
      if l = x then Int 1 else
      let c,y = dest_mul l in
      if y = x then dest_int_const c else Int 0
  with Failure _ -> try
      let c,y = dest_mul tm in
      if y = x then dest_int_const c else Int 0
  with Failure _ -> Int 1;;

(* ------------------------------------------------------------------------- *)
(* Find (always positive) LCM of all the multiples of x in formula tm.       *)
(* ------------------------------------------------------------------------- *)

let lcm_num x y = abs_num((x */ y) // gcd_num x y);;

let rec formlcm x tm =
  if is_neg tm then formlcm x (rand tm)
  else if is_conj tm or is_disj tm or is_imp tm or is_iff tm then
     lcm_num (formlcm x (lhand tm)) (formlcm x (rand tm))
  else if is_forall tm or is_exists tm then
     formlcm x (body(rand tm))
  else if not(mem x (frees tm)) then Int 1
  else let c = coefficient x (rand tm) in
       if c =/ Int 0 then Int 1 else c;;

(* ------------------------------------------------------------------------- *)
(* Switch from "x [+ ...]" to "&1 * x [+ ...]" to suit later proforma.       *)
(* ------------------------------------------------------------------------- *)

let MULTIPLY_1_CONV =
  let conv_0 = REWR_CONV(INT_ARITH `x = &1 * x`)
  and conv_1 = REWR_CONV(INT_ARITH `x + a = &1 * x + a`) in
  fun vars tm ->
    let x = hd vars in
    if tm = x then conv_0 tm
    else if is_add tm & lhand tm = x then conv_1 tm
    else REFL tm;;

(* ------------------------------------------------------------------------- *)
(* Adjust all coefficients of x (head variable) to match l in formula tm.    *)
(* ------------------------------------------------------------------------- *)

let ADJUSTCOEFF_CONV =
  let op_eq = `(=):int->int->bool`
  and op_lt = `(<):int->int->bool`
  and op_gt = `(>):int->int->bool`
  and op_divides = `(divides):int->int->bool`
  and c_tm = `c:int`
  and d_tm = `d:int`
  and e_tm = `e:int` in
  let pth_divides = prove
   (`~(d = &0) ==> (c divides e <=> (d * c) divides (d * e))`,
    SIMP_TAC[divides; GSYM INT_MUL_ASSOC; INT_EQ_MUL_LCANCEL])
  and pth_eq = prove
   (`~(d = &0) ==> ((&0 = e) <=> (&0 = d * e))`,
    DISCH_TAC THEN CONV_TAC(BINOP_CONV SYM_CONV) THEN
    ASM_REWRITE_TAC[INT_ENTIRE])
  and pth_lt_pos = prove
   (`&0 < d ==> (&0 < e <=> &0 < d * e)`,
    DISCH_TAC THEN SUBGOAL_THEN `&0 < e <=> d * &0 < d * e` SUBST1_TAC THENL
     [ASM_SIMP_TAC[INT_LT_LMUL_EQ]; REWRITE_TAC[INT_MUL_RZERO]])
  and pth_gt_pos = prove
   (`&0 < d ==> (&0 > e <=> &0 > d * e)`,
    DISCH_TAC THEN REWRITE_TAC[INT_GT] THEN
    SUBGOAL_THEN `e < &0 <=> d * e < d * &0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[INT_LT_LMUL_EQ]; REWRITE_TAC[INT_MUL_RZERO]])
  and true_tm = `T` and false_tm = `F` in
  let pth_lt_neg = prove
   (`d < &0 ==> (&0 < e <=> &0 > d * e)`,
    REWRITE_TAC[INT_ARITH `&0 > d * e <=> &0 < --d * e`;
                INT_ARITH `d < &0 <=> &0 < --d`; pth_lt_pos])
  and pth_gt_neg = prove
   (`d < &0 ==> (&0 > e <=> &0 < d * e)`,
    REWRITE_TAC[INT_ARITH `&0 < d * e <=> &0 > --d * e`;
                INT_ARITH `d < &0 <=> &0 < --d`; pth_gt_pos]) in
  let rec ADJUSTCOEFF_CONV vars l tm =
    if tm = true_tm or tm = false_tm then REFL tm
    else if is_exists tm or is_forall tm then
      BINDER_CONV (ADJUSTCOEFF_CONV vars l) tm
    else if is_neg tm then
      RAND_CONV (ADJUSTCOEFF_CONV vars l) tm
    else if is_conj tm or is_disj tm or is_imp tm or is_iff tm then
      BINOP_CONV (ADJUSTCOEFF_CONV vars l) tm
    else
      let lop,t = dest_comb tm in
      let op,z = dest_comb lop in
      let c = coefficient (hd vars) t in
      if c =/ Int 0 then REFL tm else
      let th1 =
        if c =/ l then REFL tm else
        let m = l // c in
        let th0 = if op = op_eq then pth_eq
                  else if op = op_divides then pth_divides
                  else if op = op_lt then
                    if m >/ Int 0 then pth_lt_pos else pth_lt_neg
                  else if op = op_gt then
                    if m >/ Int 0 then pth_gt_pos else pth_gt_neg
                  else failwith "ADJUSTCOEFF_CONV: unknown predicate" in
        let th1 = INST [mk_int_const m,d_tm; z,c_tm; t,e_tm] th0 in
        let tm1 = lhand(concl th1) in
        let th2 = if is_neg tm1 then EQF_ELIM(INT_EQ_CONV(rand tm1))
                  else EQT_ELIM(INT_LT_CONV tm1) in
        let th3 = MP th1 th2 in
        if op = op_divides then
          let th3 = MP th1 th2 in
          let tm2 = rand(concl th3) in
          let l,r = dest_comb tm2 in
          let th4 = AP_TERM (rator l) (INT_MUL_CONV (rand l)) in
          let th5 = AP_THM th4 r in
          let tm3 = rator(rand(concl th5)) in
          let th6 = TRANS th5 (AP_TERM tm3 (LINEAR_CMUL vars m t)) in
          TRANS th3 th6
        else
          let tm2 = rator(rand(concl th3)) in
          TRANS th3 (AP_TERM tm2 (LINEAR_CMUL vars m t)) in
      if l =/ Int 1 then
        CONV_RULE(funpow 2 RAND_CONV (MULTIPLY_1_CONV vars)) th1
      else th1 in
  ADJUSTCOEFF_CONV;;

(* ------------------------------------------------------------------------- *)
(* Now normalize all the x terms to have same coefficient and eliminate it.  *)
(* ------------------------------------------------------------------------- *)

let NORMALIZE_COEFF_CONV =
  let c_tm = `c:int`
  and pth = prove
   (`(?x. P(c * x)) <=> (?x. c divides x /\ P x)`,
    REWRITE_TAC[GSYM EXISTS_MULTIPLE_THM]) in
  let NORMALIZE_COEFF_CONV vars tm =
    let x,bod = dest_exists tm in
    let l = formlcm x tm in
    let th1 = ADJUSTCOEFF_CONV (x::vars) l tm in
    let th2 = if l =/ Int 1 then EXISTS_MULTIPLE_THM_1
              else INST [mk_int_const l,c_tm] pth in
    TRANS th1 (REWR_CONV th2 (rand(concl th1))) in
  NORMALIZE_COEFF_CONV;;

(* ------------------------------------------------------------------------- *)
(* Convert to shadow syntax.                                                 *)
(* ------------------------------------------------------------------------- *)

let SHADOW_CONV =
  let pth_trivial = prove
   (`P = interp x (Nox P)`,
    REWRITE_TAC[interp])
  and pth_composite = prove
   (`(interp x p /\ interp x q <=> interp x (And p q)) /\
     (interp x p \/ interp x q <=> interp x (Or p q))`,
    REWRITE_TAC[interp])
  and pth_literal_nontrivial = prove
   (`(&0 > x + e <=> interp x (Lt e)) /\
     (&0 < x + e <=> interp x (Gt e)) /\
     ((&0 = x + e) <=> interp x (Eq e)) /\
     (~(&0 = x + e) <=> interp x (Ne e)) /\
     (c divides (x + e) <=> interp x (Divides c e)) /\
     (~(c divides (x + e)) <=> interp x (Ndivides c e))`,
    REWRITE_TAC[interp; INT_ADD_RID] THEN INT_ARITH_TAC)
  and  pth_literal_trivial = prove
   (`(&0 > x <=> interp x (Lt(&0))) /\
     (&0 < x <=> interp x (Gt(&0))) /\
     ((&0 = x) <=> interp x (Eq(&0))) /\
     (~(&0 = x) <=> interp x (Ne(&0))) /\
     (c divides x <=> interp x (Divides c (&0))) /\
     (~(c divides x) <=> interp x (Ndivides c (&0)))`,
    REWRITE_TAC[interp; INT_ADD_RID] THEN INT_ARITH_TAC) in
  let rewr_composite = GEN_REWRITE_CONV I [pth_composite]
  and rewr_literal = GEN_REWRITE_CONV I [pth_literal_nontrivial] ORELSEC
                     GEN_REWRITE_CONV I [pth_literal_trivial]
  and x_tm = `x:int` and p_tm = `P:bool` in
  let rec SHADOW_CONV x tm =
    if not (mem x (frees tm)) then
       INST [tm,p_tm; x,x_tm] pth_trivial
    else if is_conj tm or is_disj tm then
      let l,r = try dest_conj tm with Failure _ -> dest_disj tm in
      let thl = SHADOW_CONV x l and thr = SHADOW_CONV x r in
      let th1 = MK_COMB(AP_TERM (rator(rator tm)) thl,thr) in
      TRANS th1 (rewr_composite(rand(concl th1)))
    else rewr_literal tm in
  fun tm ->
    let x,bod = dest_exists tm in
    MK_EXISTS x (SHADOW_CONV x bod);;

(* ------------------------------------------------------------------------- *)
(* Get the LCM of the dividing things.                                       *)
(* ------------------------------------------------------------------------- *)

let dplcm =
  let divides_tm = `Divides`
  and ndivides_tm = `Ndivides`
  and and_tm = `And`
  and or_tm = `Or` in
  let rec dplcm tm =
    let hop,args = strip_comb tm in
    if hop = divides_tm or hop = ndivides_tm then dest_int_const (hd args)
    else if hop = and_tm or hop = or_tm
    then end_itlist lcm_num (map dplcm args)
    else Int 1 in
  dplcm;;

(* ------------------------------------------------------------------------- *)
(* Conversion for true formulas "(--) &m divides (--) &n".                   *)
(* ------------------------------------------------------------------------- *)

let PROVE_DIVIDES_CONV_POS =
  let pth = prove
   (`(p * m = n) ==> &p divides &n`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[divides] THEN EXISTS_TAC `&m` THEN
    REWRITE_TAC[INT_OF_NUM_MUL])
  and m_tm = `m:num` and n_tm = `n:num` and p_tm = `p:num` in
  fun tm ->
    let n = rand(rand tm)
    and p = rand(lhand tm) in
    let m = mk_numeral(dest_numeral n // dest_numeral p) in
    let th1 = INST [m,m_tm; n,n_tm; p,p_tm] pth in
    EQT_INTRO(MP th1 (NUM_MULT_CONV (lhand(lhand(concl th1)))));;

let PROVE_DIVIDES_CONV =
  GEN_REWRITE_CONV REPEATC [DIVIDES_LNEG; DIVIDES_RNEG] THENC
  PROVE_DIVIDES_CONV_POS;;

(* ------------------------------------------------------------------------- *)
(* General version that works for positive and negative.                     *)
(* ------------------------------------------------------------------------- *)

let INT_DIVIDES_NUM = prove
 (`&p divides &n <=> ?m. (n = p * m)`,
  REWRITE_TAC[divides] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:int` MP_TAC) THEN
    DISJ_CASES_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC)
     (SPEC `x:int` INT_IMAGE) THEN
    DISCH_THEN(MP_TAC o AP_TERM `abs:int->int`) THEN
    REWRITE_TAC[INT_ABS_MUL; INT_ABS_NUM; INT_ABS_NEG] THEN
    REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN MESON_TAC[];
    MESON_TAC[INT_OF_NUM_MUL]]);;

let INT_DIVIDES_POS_CONV =
  let pth = prove
   (`(&p divides &n) <=> (p = 0) /\ (n = 0) \/ ~(p = 0) /\ (n MOD p = 0)`,
    REWRITE_TAC[INT_DIVIDES_NUM] THEN
    ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN EQ_TAC THENL
     [ASM_MESON_TAC[MOD_MULT];
      DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIVISION) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[MULT_SYM]]) in
  GEN_REWRITE_CONV I [pth] THENC NUM_REDUCE_CONV;;

let INT_DIVIDES_CONV =
  GEN_REWRITE_CONV REPEATC [DIVIDES_LNEG; DIVIDES_RNEG] THENC
  INT_DIVIDES_POS_CONV;;

(* ------------------------------------------------------------------------- *)
(* Conversion for "alldivide d p" (which should be true!)                    *)
(* ------------------------------------------------------------------------- *)

let ALLDIVIDE_CONV =
  let pth_atom = prove
   (`(alldivide d (Lt e) <=> T) /\
     (alldivide d (Gt e) <=> T) /\
     (alldivide d (Eq e) <=> T) /\
     (alldivide d (Ne e) <=> T) /\
     (alldivide d (Nox P) <=> T)`,
    REWRITE_TAC[alldivide])
  and pth_div = prove
    (`(alldivide d (Divides c e) <=> c divides d) /\
      (alldivide d (Ndivides c e) <=> c divides d)`,
     REWRITE_TAC[alldivide])
  and pth_comp = prove
   (`(alldivide d (And p q) <=> alldivide d p /\ alldivide d q) /\
     (alldivide d (Or p q) <=> alldivide d p /\ alldivide d q)`,
    REWRITE_TAC[alldivide])
  and pth_taut = TAUT `(T /\ T <=> T)` in
  let basnet =
    itlist (fun th -> enter [] (lhand(concl th),REWR_CONV th))
           (CONJUNCTS pth_atom)
           (itlist (fun th -> enter [] (lhand(concl th),
                                        REWR_CONV th THENC PROVE_DIVIDES_CONV))
                   (CONJUNCTS pth_div) empty_net)
  and comp_rewr = GEN_REWRITE_CONV I [pth_comp] in
  let rec alldivide_conv tm =
    try tryfind (fun f -> f tm) (lookup tm basnet) with Failure _ ->
    let th = (comp_rewr THENC BINOP_CONV alldivide_conv) tm in
    TRANS th pth_taut in
  alldivide_conv;;

(* ------------------------------------------------------------------------- *)
(* Conversion for "?b. b IN bset p /\ P b";;                                 *)
(* ------------------------------------------------------------------------- *)

let EXISTS_IN_BSET_CONV =
  let pth_false = prove
   (`((?b. b IN bset (Lt e) /\ P b) <=> F) /\
     ((?b. b IN bset (Divides c e) /\ P b) <=> F) /\
     ((?b. b IN bset (Ndivides c e) /\ P b) <=> F) /\
     ((?b. b IN bset(Nox Q) /\ P b) <=> F)`,
    REWRITE_TAC[bset; NOT_IN_EMPTY])
  and pth_neg = prove
   (`((?b. b IN bset (Gt e) /\ P b) <=> P(--e)) /\
     ((?b. b IN bset (Ne e) /\ P b) <=> P(--e))`,
    REWRITE_TAC[bset; IN_SING; INT_MUL_LID; UNWIND_THM2])
  and pth_add = prove
   (`(?b. b IN bset (Eq e) /\ P b) <=> P(--(e + &1))`,
    REWRITE_TAC[bset; IN_SING; INT_MUL_LID; UNWIND_THM2])
  and pth_comp = prove
   (`((?b. b IN bset (And p q) /\ P b) <=>
              (?b. b IN bset p /\ P b) \/
              (?b. b IN bset q /\ P b)) /\
     ((?b. b IN bset (Or p q) /\ P b) <=>
              (?b. b IN bset p /\ P b) \/
                   (?b. b IN bset q /\ P b))`,
    REWRITE_TAC[bset; IN_UNION] THEN MESON_TAC[])
  and taut = TAUT `(F \/ P <=> P) /\ (P \/ F <=> P)` in
  let conv_neg vars =
    LAND_CONV(LAND_CONV(POLYNOMIAL_NEG_CONV vars))
  and conv_add vars =
    LAND_CONV(LAND_CONV(RAND_CONV(POLYNOMIAL_ADD_CONV vars) THENC
                        POLYNOMIAL_NEG_CONV vars))
  and conv_comp = GEN_REWRITE_CONV I [pth_comp] in
  let net1 =
    itlist (fun th -> enter [] (lhand(concl th),K (REWR_CONV th)))
           (CONJUNCTS pth_false) empty_net in
  let net2 =
    itlist (fun th -> enter [] (lhand(concl th),
        let cnv = K (REWR_CONV th) in fun v -> cnv v THENC conv_neg v))
           (CONJUNCTS pth_neg) net1 in
  let basnet =
    enter [] (lhand(concl pth_add),
        let cnv = K (REWR_CONV pth_add) in fun v -> cnv v THENC conv_add v)
            net2 in
  let rec baseconv vars tm =
    try tryfind (fun f -> f vars tm) (lookup tm basnet) with Failure _ ->
    (conv_comp THENC BINOP_CONV (baseconv vars)) tm in
  let finconv =
    GEN_REWRITE_CONV DEPTH_CONV [taut] THENC
    PURE_REWRITE_CONV [DISJ_ACI] in
  fun vars tm -> (baseconv vars THENC finconv) tm;;

(* ------------------------------------------------------------------------- *)
(* Naive conversion for "minusinf p".                                        *)
(* ------------------------------------------------------------------------- *)

let MINUSINF_CONV = GEN_REWRITE_CONV TOP_SWEEP_CONV [minusinf];;

(* ------------------------------------------------------------------------- *)
(* Conversion for "interp s p" where s is a canonical linear form.           *)
(* ------------------------------------------------------------------------- *)

let INTERP_CONV =
  let pth_trivial = prove
   (`interp x (Nox P) <=> P`,
    REWRITE_TAC[interp])
  and pth_comp = prove
   (`(interp x (And p q) <=> interp x p /\ interp x q) /\
     (interp x (Or p q) <=> interp x p \/ interp x q)`,
    REWRITE_TAC[interp])
  and pth_pos,pth_neg = (CONJ_PAIR o prove)
   (`((interp x (Lt e)         <=> &0 > x + e) /\
      (interp x (Gt e)         <=> &0 < x + e) /\
      (interp x (Eq e)         <=> (&0 = x + e)) /\
      (interp x (Divides c e)  <=> c divides (x + e))) /\
     ((interp x (Ne e)         <=> ~(&0 = x + e)) /\
      (interp x (Ndivides c e) <=> ~(c divides (x + e))))`,
    REWRITE_TAC[interp] THEN INT_ARITH_TAC) in
  let conv_pos vars = RAND_CONV(POLYNOMIAL_ADD_CONV vars)
  and conv_neg vars = RAND_CONV(RAND_CONV(POLYNOMIAL_ADD_CONV vars))
  and conv_comp = GEN_REWRITE_CONV I [pth_comp] in
  let net1 =
    itlist (fun th -> enter [] (lhand(concl th),K (REWR_CONV th)))
           (CONJUNCTS pth_trivial) empty_net in
  let net2 =
    itlist (fun th -> enter [] (lhand(concl th),
        let cnv = K (REWR_CONV th) in fun v -> cnv v THENC conv_pos v))
           (CONJUNCTS pth_pos) net1 in
  let basnet =
    itlist (fun th -> enter [] (lhand(concl th),
        let cnv = K (REWR_CONV th) in fun v -> cnv v THENC conv_neg v))
           (CONJUNCTS pth_neg) net2 in
  let rec baseconv vars tm =
    try tryfind (fun f -> f vars tm) (lookup tm basnet) with Failure _ ->
    (conv_comp THENC BINOP_CONV (baseconv vars)) tm in
  baseconv;;

(* ------------------------------------------------------------------------- *)
(* Expand `?j. &1 <= j /\ j <= &[n] /\ P[j]` cases.                          *)
(* ------------------------------------------------------------------------- *)

let EXPAND_INT_CASES_CONV =
  let pth_base = prove
   (`(?j. n <= j /\ j <= n /\ P(j)) <=> P(n)`,
    MESON_TAC[INT_LE_ANTISYM])
  and pth_step = prove
   (`(?j. &1 <= j /\ j <= &(SUC n) /\ P(j)) <=>
     (?j. &1 <= j /\ j <= &n /\ P(j)) \/ P(&(SUC n))`,
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
    REWRITE_TAC[INT_ARITH `x <= y + &1 <=> (x = y + &1) \/ x < y + &1`] THEN
    REWRITE_TAC[INT_LT_DISCRETE; INT_LE_RADD] THEN
    MESON_TAC[INT_ARITH `&0 <= x ==> &1 <= x + &1`; INT_POS; INT_LE_REFL]) in
  let base_conv = REWR_CONV pth_base
  and step_conv =
   BINDER_CONV(RAND_CONV(LAND_CONV(funpow 2 RAND_CONV num_CONV))) THENC
   REWR_CONV pth_step THENC
   RAND_CONV(ONCE_DEPTH_CONV NUM_SUC_CONV) in
  let rec conv tm =
    try base_conv tm with Failure _ ->
    (step_conv THENC LAND_CONV conv) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Canonicalize "t + c" in all "interp (t + c) P"s assuming t is canonical.  *)
(* ------------------------------------------------------------------------- *)

let CANON_INTERP_ADD =
  let pat = `interp (t + c) P` in
  fun vars ->
    let net = net_of_conv pat (LAND_CONV(POLYNOMIAL_ADD_CONV vars))
              empty_net in
    ONCE_DEPTH_CONV(REWRITES_CONV net);;

(* ------------------------------------------------------------------------- *)
(* Conversion to evaluate constant expressions.                              *)
(* ------------------------------------------------------------------------- *)

let EVAL_CONSTANT_CONV =
  let net =
      itlist (uncurry net_of_conv)
       ([`x < y`,INT_LT_CONV;
         `x > y`,INT_GT_CONV;
         `x:int = y`,INT_EQ_CONV;
         `x divides y`,INT_DIVIDES_CONV] @
        map (fun t -> t,REWR_CONV(REWRITE_CONV[] t))
            [`~F`; `~T`; `a /\ T`; `T /\ a`; `a /\ F`; `F /\ a`;
             `a \/ T`; `T \/ a`; `a \/ F`; `F \/ a`])
      empty_net in
    DEPTH_CONV(REWRITES_CONV net);;

(* ------------------------------------------------------------------------- *)
(* Basic quantifier elimination conversion.                                  *)
(* ------------------------------------------------------------------------- *)

let BASIC_COOPER_CONV =
  let p_tm = `p:cform`
  and d_tm = `d:int` in
  let pth_B = SPECL [p_tm; d_tm] MAINTHM_B in
  fun vars tm ->
    let x,bod = dest_exists tm in
    let th1 = (NORMALIZE_COEFF_CONV vars THENC SHADOW_CONV) tm in
    let p = rand(snd(dest_exists(rand(concl th1)))) in
    let th2 = INST [p,p_tm; mk_int_const(dplcm p),d_tm] pth_B in
    let tm2a,tm2b = dest_conj(lhand(concl th2)) in
    let th3 =
      CONJ (EQT_ELIM(ALLDIVIDE_CONV tm2a)) (EQT_ELIM(INT_LT_CONV tm2b)) in
    let th4 = TRANS th1 (MP th2 th3) in
    let th5 = CONV_RULE(RAND_CONV(BINDER_CONV(funpow 2 RAND_CONV(LAND_CONV
                        MINUSINF_CONV)))) th4 in
    let th6 = CONV_RULE(RAND_CONV(BINDER_CONV(funpow 3 RAND_CONV
                        (EXISTS_IN_BSET_CONV vars)))) th5 in
    let th7 = CONV_RULE(RAND_CONV EXPAND_INT_CASES_CONV) th6 in
    let th8 = CONV_RULE(RAND_CONV(CANON_INTERP_ADD vars)) th7 in
    let th9 = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV(INTERP_CONV vars))) th8 in
    CONV_RULE(RAND_CONV EVAL_CONSTANT_CONV) th9;;

(* ------------------------------------------------------------------------- *)
(* NNF transformation that also eliminates negated inequalities.             *)
(* ------------------------------------------------------------------------- *)

let NNF_POSINEQ_CONV =
  let pth = prove
   (`(~(&0 < x) <=> &0 < &1 - x) /\
     (~(&0 > x) <=> &0 < &1 + x)`,
    REWRITE_TAC[INT_NOT_LT; INT_GT] THEN
    REWRITE_TAC[INT_LT_DISCRETE; INT_GT_DISCRETE] THEN
    INT_ARITH_TAC) in
  let conv1 vars = REWR_CONV(CONJUNCT1 pth) THENC
                   RAND_CONV (POLYNOMIAL_SUB_CONV vars)
  and conv2 vars = REWR_CONV(CONJUNCT2 pth) THENC
                   RAND_CONV (POLYNOMIAL_ADD_CONV vars)
  and pat1 = `~(&0 < x)` and pat2 = `~(&0 > x)`
  and net = itlist (fun t -> net_of_conv (lhand t) (REWR_CONV(TAUT t)))
                   [`~(~ p) <=> p`; `~(p /\ q) <=> ~p \/ ~q`;
                    `~(p \/ q) <=> ~p /\ ~q`] empty_net in
  fun vars ->
   let net' = net_of_conv pat1 (conv1 vars)
               (net_of_conv pat2 (conv2 vars) net) in
   TOP_SWEEP_CONV(REWRITES_CONV net');;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let COOPER_CONV =
  let FORALL_ELIM_CONV = GEN_REWRITE_CONV I
   [prove(`(!x. P x) <=> ~(?x. ~(P x))`,MESON_TAC[])]
  and not_tm = `(~)` in
  let rec conv vars tm =
    if is_conj tm or is_disj tm then
      let lop,r = dest_comb tm in
      let op,l = dest_comb lop in
      MK_COMB(AP_TERM op (conv vars l),conv vars r)
    else if is_neg tm then
      let l,r = dest_comb tm in
      AP_TERM l (conv vars r)
    else if is_exists tm then
      let x,bod = dest_exists tm in
      let th1 = MK_EXISTS x (conv (x::vars) bod) in
      TRANS th1 (BASIC_COOPER_CONV vars (rand(concl th1)))
    else if is_forall tm then
      let x,bod = dest_forall tm in
      let th1 = AP_TERM not_tm (conv (x::vars) bod) in
      let th2 = CONV_RULE(RAND_CONV (NNF_POSINEQ_CONV (x::vars))) th1 in
      let th3 = MK_EXISTS x th2 in
      let th4 = CONV_RULE(RAND_CONV (BASIC_COOPER_CONV vars)) th3 in
      let th5 = CONV_RULE(RAND_CONV (NNF_POSINEQ_CONV (x::vars)))
          (AP_TERM not_tm th4) in
      TRANS (FORALL_ELIM_CONV tm) th5
    else REFL tm in
  let init_CONV =
    PRESIMP_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [INT_ABS;
      INT_ARITH `max m n = if m <= n then n else m`;
      INT_ARITH `min m n = if m <= n then m else n`] THENC
    CONDS_ELIM_CONV THENC NNF_CONV in
  fun tm ->
    let vars = frees tm in
    let th1 = (init_CONV THENC LINEARIZE_CONV vars) tm in
    let th2 = TRANS th1 (conv vars (rand(concl th1))) in
    TRANS th2 (EVAL_CONSTANT_CONV(rand(concl th2)));;

(* ------------------------------------------------------------------------- *)
(* Examples from the book.                                                   *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV `!x y. x < y ==> &2 * x + &1 < &2 * y`;;

time COOPER_CONV `!x y. ~(&2 * x + &1 = &2 * y)`;;

time COOPER_CONV
   `?x y. x > &0 /\ y >= &0 /\ (&3 * x - &5 * y = &1)`;;

time COOPER_CONV `?x y z. &4 * x - &6 * y = &1`;;

time COOPER_CONV `!x. b < x ==> a <= x`;;

time COOPER_CONV `!x. a < &3 * x ==> b < &3 * x`;;

time COOPER_CONV `!x y. x <= y ==> &2 * x + &1 < &2 * y`;;

time COOPER_CONV `(?d. y = &65 * d) ==> (?d. y = &5 * d)`;;

time COOPER_CONV `!y. (?d. y = &65 * d) ==> (?d. y = &5 * d)`;;

time COOPER_CONV `!x y. ~(&2 * x + &1 = &2 * y)`;;

time COOPER_CONV `!x y z. (&2 * x + &1 = &2 * y) ==> x + y + z > &129`;;

time COOPER_CONV `!x. a < x ==> b < x`;;

time COOPER_CONV `!x. a <= x ==> b < x`;;

(* ------------------------------------------------------------------------- *)
(* Formula examples from Cooper's paper.                                     *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV `!a b. ?x. a < &20 * x /\ &20 * x < b`;;

time COOPER_CONV `?x. a < &20 * x /\ &20 * x < b`;;

time COOPER_CONV `!b. ?x. a < &20 * x /\ &20 * x < b`;;

time COOPER_CONV `!a. ?b. a < &4 * b + &3 * a \/ (~(a < b) /\ a > b + &1)`;;

time COOPER_CONV `?y. !x. x + &5 * y > &1 /\ &13 * x - y > &1 /\ x + &2 < &0`;;

(* ------------------------------------------------------------------------- *)
(* More of my own.                                                           *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV `!x y. x >= &0 /\ y >= &0
                  ==> &12 * x - &8 * y < &0 \/ &12 * x - &8 * y > &2`;;

time COOPER_CONV `?x y. &5 * x + &3 * y = &1`;;

time COOPER_CONV `?x y. &5 * x + &10 * y = &1`;;

time COOPER_CONV `?x y. x >= &0 /\ y >= &0 /\ (&5 * x - &6 * y = &1)`;;

time COOPER_CONV `?w x y z. &2 * w + &3 * x + &4 * y + &5 * z = &1`;;

time COOPER_CONV `?x y. x >= &0 /\ y >= &0 /\ (&5 * x - &3 * y = &1)`;;

time COOPER_CONV `?x y. x >= &0 /\ y >= &0 /\ (&3 * x - &5 * y = &1)`;;

time COOPER_CONV `?x y. x >= &0 /\ y >= &0 /\ (&6 * x - &3 * y = &1)`;;

time COOPER_CONV `!x y. ~(x = &0) ==> &5 * y < &6 * x \/ &5 * y > &6 * x`;;

time COOPER_CONV
  `!x y. ~(&5 divides x) /\ ~(&6 divides y) ==> ~(&6 * x = &5 * y)`;;

time COOPER_CONV `!x y. ~(&5 divides x) ==> ~(&6 * x = &5 * y)`;;

time COOPER_CONV `!x y. ~(&6 * x = &5 * y)`;;

time COOPER_CONV `!x y. (&6 * x = &5 * y) ==> (?d. y = &3 * d)`;;

time COOPER_CONV `(&6 * x = &5 * y) ==> (?d. y = &3 * d)`;;

(* ------------------------------------------------------------------------- *)
(* Positive variant of the Bezout theorem (see the exercise).                *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV
  `!z. z > &7 ==> ?x y. x >= &0 /\ y >= &0 /\ (&3 * x + &5 * y = z)`;;

time COOPER_CONV
  `!z. z > &2 ==> ?x y. x >= &0 /\ y >= &0 /\ (&3 * x + &5 * y = z)`;;

time COOPER_CONV `!z. z <= &7 ==>
         ((?x y. x >= &0 /\ y >= &0 /\ (&3 * x + &5 * y = z)) <=>
          ~(?x y. x >= &0 /\ y >= &0 /\ (&3 * x + &5 * y = &7 - z)))`;;

(* ------------------------------------------------------------------------- *)
(* Basic result about congruences.                                           *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV `!x. ~(&2 divides x) /\ &3 divides (x - &1) <=>
                      &12 divides (x - &1) \/ &12 divides (x - &7)`;;

time COOPER_CONV `!x. ~(?m. x = &2 * m) /\ (?m. x = &3 * m + &1) <=>
                     (?m. x = &12 * m + &1) \/ (?m. x = &12 * m + &7)`;;

(* ------------------------------------------------------------------------- *)
(* Something else.                                                           *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV
 `!x. ~(&2 divides x)
      ==> &4 divides (x - &1) \/
          &8 divides (x - &1) \/
          &8 divides (x - &3) \/
          &6 divides (x - &1) \/
          &14 divides (x - &1) \/
          &14 divides (x - &9) \/
          &14 divides (x - &11) \/
          &24 divides (x - &5) \/
          &24 divides (x - &11)`;;

(* ------------------------------------------------------------------------- *)
(* Testing fix for an earlier version with negative result from formlcm.     *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV
 `!a b v_1 v_2 v_3.
    (a + &2 = b) /\ (v_3 = b - a + &1) /\ (v_2 = b - &2) /\ (v_1 = &3) ==> F`;;

(* ------------------------------------------------------------------------- *)
(* Inspired by the Collatz conjecture.                                       *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV
 `?a b. ~(a = &1) /\ ((&2 * b = a) \/ (&2 * b = &3 * a + &1)) /\
              (a = b)`;;

time COOPER_CONV
 `?a b. a > &1 /\ b > &1 /\
             ((&2 * b = a) \/ (&2 * b = &3 * a + &1)) /\
             (a = b)`;;

time COOPER_CONV
 `?b. a > &1 /\ b > &1 /\
      ((&2 * b = a) \/ (&2 * b = &3 * a + &1)) /\
      ((&2 * a = b) \/ (&2 * a = &3 * b + &1))`;;

(*************** These seem to take a long time

time COOPER_CONV
 `?a b. a > &1 /\ b > &1 /\
             ((&2 * b = a) \/ (&2 * b = &3 * a + &1)) /\
             ((&2 * a = b) \/ (&2 * a = &3 * b + &1))`;;

let fm = (dnf ** parse)
 `((2 * b = a) \/ (2 * b = &3 * a + 1)) /\
  ((2 * c = b) \/ (2 * c = &3 * b + 1)) /\
  ((2 * d = c) \/ (2 * d = &3 * c + 1)) /\
  ((2 * e = d) \/ (2 * e = &3 * d + 1)) /\
  ((2 * f = e) \/ (2 * f = &3 * e + 1)) /\
  (f = a)`;;

let fms =
  map (itlist (fun x p -> Exists(x,And(Atom(R(`>`,[Var x; Fn(`1`,[])])),p)))
              [`b`; `c`; `d`; `e`; `f`])
      (disjuncts fm);;

let fm = el &15 fms;;
integer_qelim fm;;

******************)

(* ------------------------------------------------------------------------- *)
(* More old examples.                                                        *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV
 `?x. &5 * x + x + x < x \/
      (y = &7 - x) /\ &33 + z < x /\ x + &1 <= &2 * y \/
      &3 divides &4 * x + z /\ (x + y + z = &7 * z)`;;

time COOPER_CONV
 `?x. &5 * x + x + x < x \/
      (y = &7 - x) /\
      &33 + z < x /\
      x + &1 <= &2 * y \/
      &3 divides (&4 * x + z) /\
      (x + y + z = &7 * z)`;;

time COOPER_CONV
 `?x. &5 * x + x + x < x \/
      (y = &7 - x) /\
      &33 + z < x /\
      x + &1 <= &2 * y \/
      &3 divides (&4 * x + z) /\
      (x + y + z = &7 * z)`;;

(**** This also seems very slow; one quantifier less maybe?

time COOPER_CONV
 `?z y x. &5 * x + x + x < x \/
          (y = &7 - x) /\
          &33 + z < x /\
          x + &1 <= &2 * y \/
          &3 divides (&4 * x + z) /\
          (x + y + z = &7 * z)`;;

time COOPER_CONV                         
 `?y x. &5 * x + x + x < x \/
        (y = &7 - x) /\
        &33 + z < x /\
        x + &1 <= &2 * y \/        
        &3 divides (&4 * x + z) /\                 
        (x + y + z = &7 * z)`;;

*****)

time COOPER_CONV
     `?x. x + &1 < &2 * y /\
          &3 divides (&4 * x + z) /\
          (&6 * x + y + z = &7 * z)`;;

time COOPER_CONV
     `?x. &5 * x + x + x < x \/
          (y = &7 - x) /\
          &33 + z < x /\
          x + &1 < &2 * y \/
          &3 divides (&4 * x + z) /\
          (x + y + z = &7 * z)`;;

(* ------------------------------------------------------------------------- *)
(* Stamp problem.                                                            *)
(* ------------------------------------------------------------------------- *)

time COOPER_CONV `!x. x >= &8 ==> ?u v. u >= &0 /\ v >= &0 /\
                                         (x = &3 * u + &5 * v)`;;

time COOPER_CONV `!x. x >= &10 ==> ?u v. u >= &0 /\ v >= &0 /\
                                         (x = &3 * u + &7 * v)`;;

time COOPER_CONV `!x. x >= &30 ==> ?u v. u >= &0 /\ v >= &0 /\
                                         (x = &3 * u + &7 * v)`;;

(* ------------------------------------------------------------------------- *)
(* Decision procedures in the style of INT_ARITH and ARITH_RULE.             *)
(*                                                                           *)
(* Really I should locate the free alien subterms.                           *)
(* ------------------------------------------------------------------------- *)

let INT_COOPER tm =
  let fvs = frees tm in
  let tm' = list_mk_forall(fvs,tm) in
  SPECL fvs (EQT_ELIM(COOPER_CONV tm'));;

let COOPER_RULE tm =
  let fvs = frees tm in
  let tm' = list_mk_forall(fvs,tm) in
  let th = (NUM_TO_INT_CONV THENC COOPER_CONV) tm' in
  SPECL fvs (EQT_ELIM th);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

time INT_COOPER `abs(x) < &1 ==> (x = &0)`;;

time COOPER_RULE `ODD n ==> 2 * n DIV 2 < n`;;

time COOPER_RULE `!n. EVEN(n) ==> (2 * n DIV 2 = n)`;;

time COOPER_RULE `!n. ODD n <=> 2 * n DIV 2 < n`;;

(**** This seems quite slow (maybe not very) as well
time COOPER_RULE `n DIV 3 <= n DIV 2`;;
 ****)

(*** This one too?
time COOPER_RULE `!x. ?y. if EVEN x then x = 2 * y else x = 2 * (y - 1) + 1`;;
 ***)

time COOPER_RULE `!n. n >= 8 ==> ?a b. n = 3 * a + 5 * b`;;
