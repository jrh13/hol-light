(* ========================================================================= *)
(*                                                                           *)
(*           Library of complex function vector spaces.                      *)
(*                                                                           *)
(*   (c) Copyright, Mohamed Yousri Mahmoud, Vincent Aravantinos, 2012-2013   *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <mosolim@ece.concordia.ca>, <vincent@ece.concordia.ca> *)
(*   Last update: Jan 2014                                                   *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;
needs "Functionspaces/utils.ml";;

(* ------------------------------------------------------------------------- *)
(* EMBEDDING OF REALS IN COMPLEX NUMBERS                                     *)
(* ------------------------------------------------------------------------- *)

let real_of_complex = new_definition
  `real_of_complex c = @r. c = Cx r`;;

let REAL_OF_COMPLEX = prove
  (`!c. real c ==> Cx(real_of_complex c) = c`,
  MESON_TAC[REAL;real_of_complex]);;

let REAL_OF_COMPLEX_RE = prove
  (`!c. real c ==> real_of_complex c = Re c`,
  MESON_TAC[RE_CX;REAL_OF_COMPLEX]);;

let REAL_OF_COMPLEX_CX = prove
  (`!r. real_of_complex (Cx r) = r`,
  SIMP_TAC[REAL_CX;REAL_OF_COMPLEX_RE;RE_CX]);;

let REAL_OF_COMPLEX_NORM = prove
  (`!c. real c ==> norm c = abs (real_of_complex c)`,
  IMP_REWRITE_TAC[REAL_NORM;REAL_OF_COMPLEX_RE]);;

let REAL_OF_COMPLEX_ADD = prove
  (`!x y. real x /\ real y ==>
    real_of_complex (x+y) = real_of_complex x + real_of_complex y`,
  MESON_TAC[REAL_ADD;REAL_OF_COMPLEX_RE;RE_ADD]);;

let REAL_OF_COMPLEX_SUB = prove
  (`!x y. real x /\ real y ==>
    real_of_complex (x-y) = real_of_complex x - real_of_complex y`,
  MESON_TAC[REAL_SUB;REAL_OF_COMPLEX_RE;RE_SUB]);;

let REAL_OF_COMPLEX_ZERO = prove
  (`!x y. real x ==>
    (real_of_complex x = &0 <=> x = Cx(&0))`,
  MESON_TAC[  REAL_OF_COMPLEX_RE;real;
  SIMPLE_COMPLEX_ARITH `Im x = &0 ==> (Re x = &0 <=> x = Cx(&0))`]);;

let REAL_MUL = prove
  (`!x y. real x /\ real y ==> real (x*y)`,
  REWRITE_TAC[real] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let REAL_OF_COMPLEX_MUL = prove
  (`!x y. real x /\ real y ==>
    real_of_complex (x*y) = real_of_complex x * real_of_complex y`,
  MESON_TAC[REAL_MUL;REAL_OF_COMPLEX;CX_MUL;REAL_OF_COMPLEX_CX]);;

let NORM2_ADD_REAL = prove
  (`!x y. real x /\ real y ==>
    norm (x + ii * y) pow 2 = norm x pow 2 + norm y pow 2`,
  SIMP_TAC[real;complex_norm;RE_ADD;IM_ADD;RE_MUL_II;IM_MUL_II;REAL_NEG_0;
    REAL_ADD_LID;REAL_ADD_RID;REAL_POW_ZERO;ARITH_RULE `~(2=0)`;REAL_LE_POW_2;
    SQRT_POW_2;REAL_LE_ADD]);;

let real_thms = ref [];;
let add_real_thm thm = real_thms := GIMP_IMP thm :: !real_thms;;
let add_real_thms = List.iter add_real_thm;;

let REAL_TAC ?(alternatives=[]) g =
  let is_meta_variable v = try (fst (dest_var v)).[0] = '_' with _ -> false in
  let contain_meta_variable = can (find_term is_meta_variable) in
  let MATCH_MP_TAC x =
    (fun g -> MATCH_MP_TAC x g) THEN (fun (_,concl as g) ->
      if contain_meta_variable concl then NO_TAC g else ALL_TAC g) in
  let TRY_REAL_THM = ASM (MAP_FIRST (fun x ->
    MATCH_ACCEPT_TAC x ORELSE MATCH_MP_TAC x)) !real_thms in
  let LOOP = TRY_REAL_THM ORELSE (ASM_SIMP_TAC[] THEN NO_TAC)
    ORELSE (CHANGED_TAC (ASM_SIMP_TAC[real]) THEN CONV_TAC COMPLEX_FIELD)
    ORELSE FIRST alternatives in
  (REPEAT STRIP_TAC
  THEN (fun (_,concl as g) ->
    if not (repeat rator concl = `real :complex -> bool`)
    then FAIL_TAC "bad goal" g
    else CHANGED_TAC (REPEAT (LOOP THEN REPEAT CONJ_TAC)) g)) g;;

add_real_thm REAL_MUL;;


(* ------------------------------------------------------------------------- *)
(* MAP OVER FUNCTIONS                                                        *)
(* ------------------------------------------------------------------------- *)

let fun_map2 = new_definition
  `fun_map2 (f:B->C->D) (g1:A->B) (g2:A->C) = \x. f (g1 x) (g2 x)`;;

let FUN_MAP2_THM = prove
  (`!f g1 g2 x. fun_map2 f g1 g2 x = f (g1 x) (g2 x)`,
  REWRITE_TAC[fun_map2]);;

let K_DEF = new_definition
  `K (x:A) = \y:B. x`;;

let K_THM = prove
  (`!x y. K x y = x`,
  REWRITE_TAC[K_DEF]);;

let fun_map_defs = CONJS [K_DEF;o_DEF;fun_map2];;

let FUN_MAP_THMS = CONJS [K_THM;o_THM;FUN_MAP2_THM];;


(* --------------------------------------------------------------------------- *)
(* COMPLEX VALUED FUNCTIONS                                                    *)
(* --------------------------------------------------------------------------- *)

new_type_abbrev("cfun",`:A->complex`);;
new_type_abbrev("cfunB",`:B->complex`);;
new_type_abbrev("cfunC",`:C->complex`);;

let cfun_add = new_definition
  `cfun_add:cfun->cfun->cfun = fun_map2 (+)`;;

let cfun_smul = new_definition
  `cfun_smul (a:complex) :cfun->cfun = (o) (( * ) a)`;;

let cfun_neg = new_definition
  `cfun_neg:cfun->cfun = (o) (--)`;;

let cfun_sub = new_definition
  `cfun_sub:cfun->cfun->cfun = fun_map2 (-)`;;

let cfun_zero = new_definition
  `cfun_zero:cfun = K (Cx(&0))`;;

let cfun_cnj = new_definition
  `cfun_cnj:cfun->cfun = (o) cnj`;;

let cfun_defs = CONJS [cfun_add;cfun_sub;cfun_smul;cfun_neg;cfun_cnj;cfun_zero];;

make_overloadable "%" `:A->B->B`;;
parse_as_infix("%",(25,"left"));;

let prioritize_cfun () =
  overload_interface("+",`cfun_add:cfun->cfun->cfun`);
  overload_interface("%",`cfun_smul:complex->cfun->cfun`);
  overload_interface("--",`cfun_neg : cfun->cfun`);
  overload_interface("-",`cfun_sub:cfun->cfun->cfun`);;

prioritize_cfun ();;

(* Intended restriction of FUN_EQ_THM to the type :cfun *)
let CFUN_EQ = prove
  (`!f g:cfun. f = g <=> !x. f x = g x`,
  REWRITE_TAC[FUN_EQ_THM]);;

let CFUN_TO_COMPLEX = CONJS [FUN_MAP_THMS;cfun_defs;CFUN_EQ];;


(* General tactic *)

let CFUN_ARITH_TAC =
  let lemma = MESON[] `(!x. P x <=> Q x) ==> (!x. P x) = (!x. Q x)` in
  REWRITE_TAC[CFUN_TO_COMPLEX]
  THEN (CONV_TAC COMPLEX_FIELD
     ORELSE SIMPLE_COMPLEX_ARITH_TAC
    ORELSE (REPEAT STRIP_TAC THEN CONV_TAC PRENEX_CONV
      THEN MATCH_MP_TAC lemma THEN CONV_TAC COMPLEX_FIELD));;

let CFUN_ARITH t = prove(t,CFUN_ARITH_TAC);;


(* Properties *)


let CFUN_ADD_THM = CFUN_ARITH `!f g. (f + g) x = f x + g x`;;

let CFUN_SUB = CFUN_ARITH `!f g. f - g = \x. f x - g x`;;

let CFUN_SUB_THM = CFUN_ARITH `!f g. (f - g) x = f x - g x`;;

let CFUN_ADD = CFUN_ARITH `!f g. f + g = \x. f x + g x`;;

let CFUN_ADD_THM = CFUN_ARITH `!f g. (f + g) x =  f x + g x`;;

let CFUN_SMUL = CFUN_ARITH `!a f. a % f = \x. a * f x`;;

let CFUN_NEG_LAMBDA = CFUN_ARITH `!f. --f = \x. --(f x)`;;

let CFUN_SMUL_LNEG = CFUN_ARITH `!a f. (--a) % f = --(a % f)`;;

let CFUN_SMUL_RNEG = CFUN_ARITH `!a f. a % (--f) = --(a % f)`;;

let CFUN_ADD_SYM = CFUN_ARITH `!x y. x + y = y + x`;;

let CFUN_ADD_ASSOC = CFUN_ARITH `!x y z. (x + y) + z = x + y + z`;;

let CFUN_SUB_NEG = CFUN_ARITH `!x y. x - y = x + --y`;;

let CFUN_SUB_REFL = CFUN_ARITH `!x. x - x = cfun_zero`;;

let CFUN_SMUL_LZERO = CFUN_ARITH `!x. Cx(&0) % x = cfun_zero`;;

let CFUN_ADD_LID = CFUN_ARITH `!x. cfun_zero + x = x`;;

let CFUN_ADD_RID = CFUN_ARITH `!x. x + cfun_zero = x`;;

let CFUN_SUB_RID = CFUN_ARITH `!x. x - cfun_zero = x`;;

let CFUN_SMUL_RZERO = CFUN_ARITH `!a. a % cfun_zero = cfun_zero`;;

let CFUN_ZERO_CLAUSES =
  CONJS [CFUN_SUB_REFL;CFUN_ADD_RID;CFUN_SMUL_LZERO;CFUN_SMUL_RZERO];;

let CFUN_SMUL_SYM = CFUN_ARITH `!a b x. a % (b % x) = b % (a % x)`;;

let CFUN_SUB_REFL = CFUN_ARITH `!x. x - x = cfun_zero`;;

let CFUN_SMUL_DIS = CFUN_ARITH `!a x y. a % (x + y) = a % x + a % y`;;

let CFUN_SMUL_ASSOC = CFUN_ARITH `!a b x. a % (b % x) = (a * b) % x`;;

let CFUN_ADD_RDISTRIB = CFUN_ARITH `!a b x. (a + b) % x = a % x + b % x`;;

let CFUN_SUB_RDISTRIB = CFUN_ARITH `!a b x. (a - b) % x = a % x - b % x`;;

let CFUN_SUB_RADD = CFUN_ARITH `!x y z. x - (y + z) = x - y - z`;;

let CFUN_ADD_RSUB = CFUN_ARITH `!x y z. x + (y - z) = (x + y) - z`;;

let CFUN_SUB_ADD = CFUN_ARITH `!x y z. (x - y) + z= (x + z) - y`;;

let CFUN_SUB_SUB = CFUN_ARITH `!x y z. x - (y - z) = x - y + z`;;

let CFUN_EQ_LSUB = CFUN_ARITH `!x y z. x - y = z <=> x = z + y`;;

let CFUN_EQ_RSUB = CFUN_ARITH `!x y z. x = y - z <=> x + z = y`;;

let CFUN_ZERO_ADD = CFUN_ARITH `!x y. y + x = x <=> y = cfun_zero`;;

let CFUN_SUB_LDISTRIB = CFUN_ARITH `!a x y. a % (x - y) = a % x - a % y`;;

let CFUN_ADD_LDISTRIB = CFUN_ARITH `!a x y. a % (x + y) = a % x + a % y`;;

let CFUN_SMUL_DISTRIB = CFUN_ARITH `!a b f. a % (b % f) = (a * b) % f`;;

let CFUN_SMUL_LID = CFUN_ARITH `!v. Cx(&1) % v = v`;;

let CFUN_SMUL_LID_NEG = CFUN_ARITH `!v. (--Cx(&1)) % v = --v`;;

let CFUN_EQ_NEG2 = CFUN_ARITH `!x y. --x = --y <=> x = y`;;

let CFUN_EQ_ADD_LCANCEL = CFUN_ARITH `!x y z. x + y = x + z <=> y = z`;;

let CFUN_EQ_ADD_RCANCEL = CFUN_ARITH `!x y z. x + z = y + z <=> x = y`;;

let CFUN_EQ_SUB_LCANCEL = CFUN_ARITH `!x y z. x - y = x - z <=> y = z`;;

let CFUN_EQ_SUB_RADD = CFUN_ARITH `!x y z. x - y = z <=> x = z + y`;;

let CFUN_SUB_ADD2 = CFUN_ARITH `!x y. y + x - y = x`;;

let CFUN_SUB_0 = CFUN_ARITH `!x y. x - y = cfun_zero <=> x = y`;;

let CFUN_ENTIRE = CFUN_ARITH
  `!a x. a % x = cfun_zero <=> a = Cx(&0) \/ x = cfun_zero`;;

let CFUN_EQ_SMUL_LCANCEL = CFUN_ARITH
  `!x y a. a % x = a % y <=> a = Cx(&0) \/ x = y`;;

let CFUN_EQ_SMUL_LCANCEL2 = prove
  (`!a x y. ~(a=Cx(&0)) ==> (a % x = y <=> x = inv a % y)`,
  REWRITE_TAC[CFUN_TO_COMPLEX] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC (MESON[] `(!x. P x <=> Q x) ==> (!x. P x) = (!x. Q x)`)
  THEN GEN_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

(* Sub-space *)
let is_cfun_subspace = new_definition
  `is_cfun_subspace (spc:cfun->bool) <=>
    cfun_zero IN spc /\
    !x. x IN spc ==> (!a. a % x IN spc) /\ !y. y IN spc ==> x+y IN spc`;;

let CFUN_SUBSPACE_ZERO = prove
  (`!s. is_cfun_subspace s ==> cfun_zero IN s`,
  SIMP_TAC[is_cfun_subspace]);;

let CFUN_SUBSPACE_SMUL = prove
  (`!s a x. is_cfun_subspace s /\ x IN s ==> a%x IN s`,
  SIMP_TAC[is_cfun_subspace]);;

let CFUN_SUBSPACE_ADD = prove
  (`!s x y. is_cfun_subspace s /\ x IN s /\ y IN s ==> x+y IN s`,
  SIMP_TAC[is_cfun_subspace]);;

let CFUN_SUBSPACE_NEG = prove
  (`!s x. is_cfun_subspace s /\ x IN s ==> --x IN s`,
  SIMP_TAC[GSYM CFUN_SMUL_LID_NEG;CFUN_SUBSPACE_SMUL]);;

let CFUN_SUBSPACE_SUB = prove
  (`!s x y. is_cfun_subspace s /\ x IN s /\ y IN s ==> x-y IN s`,
  SIMP_TAC[CFUN_SUB_NEG;CFUN_SUBSPACE_NEG;CFUN_SUBSPACE_ADD]);;

let CFUN_SUBSPACE_SING_CFUNZERO = prove
  (`is_cfun_subspace {cfun_zero}`,
  SIMP_TAC[is_cfun_subspace;IN_SING;CFUN_SMUL_RZERO;CFUN_ADD_RID]);;


(* ------------------------------------------------------------------------- *)
(* EMBEDDING COMPLEX NUMBERS IN CFUNS                                        *)
(* ------------------------------------------------------------------------- *)

let SING_IND,SING_REC = define_type "singleton = SING_ELT";;

let SING_EQ = prove
  (`!x. x = SING_ELT`,
  MATCH_MP_TAC SING_IND THEN REFL_TAC);;

let cfun_of_complex = new_definition
  `cfun_of_complex = K :complex->singleton->complex`;;

let CFUN_OF_COMPLEX_ADD = prove
  (`!x y. cfun_of_complex (x+y) = cfun_of_complex x + cfun_of_complex y`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_SUB = prove
  (`!x y. cfun_of_complex (x-y) = cfun_of_complex x - cfun_of_complex y`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_NEG = prove
  (`!x. cfun_of_complex (--x) = -- cfun_of_complex x`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_SMUL = prove
  (`!a x. cfun_of_complex (a*x) = a % cfun_of_complex x`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_CNJ = prove
  (`!x. cfun_of_complex (cnj x) = cfun_cnj (cfun_of_complex x)`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_ZERO = prove
  (`cfun_of_complex (Cx(&0)) = cfun_zero`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let complex_of_cfun = new_definition
  `complex_of_cfun f :complex = f SING_ELT`;;

let COMPLEX_OF_CFUN_ADD = prove
  (`!x y. complex_of_cfun (x + y) = complex_of_cfun x + complex_of_cfun y`,
  REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC);;

let COMPLEX_OF_CFUN_SUB = prove
  (`!x y. complex_of_cfun (x - y) = complex_of_cfun x - complex_of_cfun y`,
  REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC);;

let COMPLEX_OF_CFUN_NEG = prove
  (`!x. complex_of_cfun (--x) = -- complex_of_cfun x`,
  REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC);;

let COMPLEX_OF_CFUN_SMUL = prove
  (`!a x. complex_of_cfun (a % x) = a * complex_of_cfun x`,
  REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC);;

let COMPLEX_OF_CFUN_OF_COMPLEX = prove
  (`complex_of_cfun o cfun_of_complex = I`,
  REWRITE_TAC[complex_of_cfun;cfun_of_complex;o_DEF;K_THM;I_DEF]);;

let CFUN_OF_COMPLEX_OF_CFUN = prove
  (`cfun_of_complex o complex_of_cfun = I`,
  REWRITE_TAC[complex_of_cfun;cfun_of_complex;o_DEF;K_DEF;FUN_EQ_THM;I_THM]
  THEN ONCE_REWRITE_TAC[SING_EQ] THEN REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* INNER PRODUCT                                                             *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("inprod",`:cfun->cfun->complex`);;

new_type_abbrev("inner_space",`:(cfun->bool)#inprod`);;

let is_inner_space = new_definition
  `is_inner_space ((s,inprod):inner_space) <=>
    is_cfun_subspace s /\
    !x. x IN s ==>
      real (inprod x x) /\ &0 <= real_of_complex (inprod x x)
      /\ (inprod x x = Cx(&0) <=> x = cfun_zero)
      /\ !y. y IN s ==>
        cnj (inprod y x) = inprod x y /\
        (!a. inprod x (a%y) = a * (inprod x y))
        /\ !z. z IN s ==> inprod (x+y) z = inprod x z + inprod y z`;;

(* EVERY THEOREM proved using "inner_space_prove" implicitly has the assumption
 * "!s inprod. is_inner_space (s,inprod) ==>"
 *)
let inner_space_parse s =
  parse_term (`!s inprod. is_inner_space (s,inprod) ==> :` ^ s);;

let inner_space_prove (s,p) = prove(gimp_imp (inner_space_parse s),p);;
let inner_space_g s = g (gimp_imp (inner_space_parse s));;

let full_inner_space_parse s = parse_term (`!is. is_inner_space is ==> :` ^ s);;
let full_inner_space_prove (s,p) =
  prove(gimp_imp (full_inner_space_parse s),p);;
let full_inner_space_g s = g (gimp_imp (full_inner_space_parse s));;

let FORALL_INNER_SPACE_THM = prove
  (`!P. (!is:inner_space. P is) <=> !s inprod. P (s,inprod)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;


let INNER_SPACE_IS_SUBSPACE = inner_space_prove
  (`is_cfun_subspace s:`,
  SIMP_TAC[is_inner_space]);;

  let INNER_SPACE_ZERO = inner_space_prove
  (`cfun_zero IN s:`,
  MESON_TAC[INNER_SPACE_IS_SUBSPACE;CFUN_SUBSPACE_ZERO]);;

let INNER_SPACE_SMUL = inner_space_prove
  (`!x a. x IN s ==> a%x IN s:`,
  MESON_TAC[INNER_SPACE_IS_SUBSPACE;CFUN_SUBSPACE_SMUL]);;

let INNER_SPACE_ADD = inner_space_prove
  (`!x y. x IN s /\ y IN s ==> x+y IN s:`,
  MESON_TAC[INNER_SPACE_IS_SUBSPACE;CFUN_SUBSPACE_ADD]);;

let INNER_SPACE_NEG = inner_space_prove
  (`!x. x IN s ==> --x IN s:`,
  MESON_TAC[INNER_SPACE_IS_SUBSPACE;CFUN_SUBSPACE_NEG]);;

let INNER_SPACE_SUB = inner_space_prove
  (`!x y. x IN s /\ y IN s ==> x-y IN s:`,
  MESON_TAC[INNER_SPACE_IS_SUBSPACE;CFUN_SUBSPACE_SUB]);;

let INPROD_CNJ = inner_space_prove
  (`!x y. x IN s /\ y IN s ==> cnj(inprod y x) = inprod x y:`,
  SIMP_TAC[is_inner_space]);;

let INPROD_SELF_REAL = inner_space_prove
  (`!x. x IN s ==> real (inprod x x):`,
  SIMP_TAC[is_inner_space]);;

let INPROD_SELF_POS = inner_space_prove
  (`!x. x IN s ==> &0 <= real_of_complex (inprod x x):`,
  SIMP_TAC[is_inner_space]);;

let INPROD_RSMUL = inner_space_prove
  (`!x y a. x IN s /\ y IN s ==> inprod x (a%y) = a * inprod x y:`,
  SIMP_TAC[is_inner_space]);;

let INPROD_ADD_RDIST = inner_space_prove
  (`!x y z. x IN s /\ y IN s /\ z IN s
      ==> inprod (x+y) z = inprod x z + inprod y z:`,
  SIMP_TAC[is_inner_space]);;

let INPROD_ZERO_EQ = inner_space_prove
  (`!x. x IN s ==> (inprod x x = Cx(&0) <=> x = cfun_zero):`,
  SIMP_TAC[is_inner_space]);;

let INPROD_ZERO = inner_space_prove
  (`inprod cfun_zero cfun_zero = Cx(&0):`,
  SIMP_TAC[is_inner_space;is_cfun_subspace]);;

let INPROD_NORM = inner_space_prove
  (`!x. x IN s ==> real (inprod x x) /\ &0 <= real_of_complex (inprod x x):`,
  SIMP_TAC[is_inner_space]);;

add_real_thm (MESON[INPROD_SELF_REAL]
  `!s inprod x. is_inner_space (s,inprod) /\ x IN s ==> real(inprod x x)`);;

(* More involved properties *)

let INPROD_LSMUL = inner_space_prove
  (`!x y a. x IN s /\ y IN s ==> inprod (a%x) y = cnj a * inprod x y:`,
  MESON_TAC[is_inner_space;is_cfun_subspace;CNJ_MUL]);;

let INPROD_LNEG = inner_space_prove
  (`!x y. x IN s /\ y IN s ==> inprod (--x) y = --inprod x y:`,
  MESON_TAC [GSYM CFUN_SMUL_LID_NEG;INPROD_LSMUL;CNJ_NEG;CNJ_CX;
    COMPLEX_NEG_MINUS1]);;

let INPROD_SUB_RDIST = inner_space_prove
  (`!x y z. x IN s /\ y IN s /\ z IN s ==>
      inprod (x-y) z = inprod x z - inprod y z:`,
  IMP_REWRITE_TAC[CFUN_SUB_NEG;complex_sub;INPROD_ADD_RDIST;INPROD_LNEG;
    CFUN_SUBSPACE_NEG;INNER_SPACE_IS_SUBSPACE]);;

let INPROD_RNEG = inner_space_prove
  (`!x y. x IN s /\ y IN s ==> inprod x (--y) = --inprod x y:`,
  MESON_TAC[GSYM CFUN_SMUL_LID_NEG;INPROD_RSMUL;COMPLEX_NEG_MINUS1]);;

let INPROD_ADD_LDIST = inner_space_prove
  (`!x y z. x IN s /\ y IN s /\ z IN s ==>
      inprod z (x+y) = inprod z x + inprod z y:`,
  MESON_TAC[INPROD_CNJ;INNER_SPACE_IS_SUBSPACE;CFUN_SUBSPACE_ADD;
    INPROD_ADD_RDIST;CNJ_ADD]);;

let INPROD_SUB_LDIST = inner_space_prove
  (`!x y z. x IN s /\ y IN s /\ z IN s ==>
    inprod z (x-y) = inprod z x - inprod z y:`,
  IMP_REWRITE_TAC[CFUN_SUB_NEG;complex_sub;INPROD_ADD_LDIST;INPROD_RNEG;
    CFUN_SUBSPACE_NEG;INNER_SPACE_IS_SUBSPACE]);;

let INPROD_RZERO = inner_space_prove
  (`!x. x IN s ==> inprod x cfun_zero = Cx(&0):`,
  IMP_REWRITE_TAC[GSYM CFUN_SMUL_LZERO;INPROD_RSMUL;COMPLEX_MUL_LZERO]);;

let INPROD_LZERO = inner_space_prove
  (`!x. x IN s ==> inprod cfun_zero x = Cx(&0):`,
  IMP_REWRITE_TAC[GSYM CFUN_SMUL_LZERO;INPROD_LSMUL;CNJ_CX;COMPLEX_MUL_LZERO]);;

let INPROD_SELF_CNJ = inner_space_prove
  (`!x. x IN s ==> cnj (inprod x x) = inprod x x:`,
  SIMP_TAC[GSYM REAL_CNJ;is_inner_space]);;

let INPROD_ADD_CNJ = inner_space_prove
  (`!x y. x IN s /\ y IN s ==> inprod x y + inprod y x =
   Cx(&2 * Re (inprod x y)):`,
  IMP_REWRITE_TAC[GSYM COMPLEX_ADD_CNJ;INPROD_CNJ]);;

let INPROD_SELF_NORM = inner_space_prove
  (`!x. x IN s ==> norm (inprod x x) = real_of_complex (inprod x x):`,
  MESON_TAC[is_inner_space;REAL_OF_COMPLEX;COMPLEX_NORM_CX;REAL_ABS_REFL]);;

let INPROD_SELF_RE = inner_space_prove
  (`!x. x IN s ==> real_of_complex (inprod x x) = Re (inprod x x):`,
  MESON_TAC[is_inner_space;REAL_OF_COMPLEX_RE]);;

(* Surjection holds in finite dimension only *)
let INPROD_INJ = inner_space_prove
  (`!x y. x IN s /\ y IN s ==> (inprod x = inprod y <=> x = y):`,
  TARGET_REWRITE_TAC[GSYM CFUN_SUB_0] (GSYM INPROD_ZERO_EQ)
  THEN IMP_REWRITE_TAC [INPROD_SUB_RDIST;COMPLEX_SUB_0;CFUN_SUBSPACE_SUB;
    INNER_SPACE_IS_SUBSPACE]);;

let INPROD_INJ_ALT = inner_space_prove
  (`!x y. x IN s /\ y IN s
    ==> ((!z. z IN s ==> inprod x z = inprod y z) <=> x = y):`,
  TARGET_REWRITE_TAC[GSYM CFUN_SUB_0] (GSYM INPROD_ZERO_EQ)
  THEN IMP_REWRITE_TAC [INPROD_SUB_RDIST;COMPLEX_SUB_0;CFUN_SUBSPACE_SUB;
  INNER_SPACE_IS_SUBSPACE]);;


let INPROD_NEG = inner_space_prove
  (`!x y. x IN s /\ y IN s ==> inprod (--x) (--y) = inprod x y:`,
   IMP_REWRITE_TAC[CFUN_SUBSPACE_NEG;INNER_SPACE_IS_SUBSPACE;INPROD_RNEG
   ;INPROD_LNEG;COMPLEX_NEG_NEG]);;
(* TODO RIESZ *)


(* ------------------------------------------------------------------------- *)
(* ORTHOGONALITY                                                             *)
(* ------------------------------------------------------------------------- *)

let are_orthogonal = new_definition
  `are_orthogonal ((s,inprod):inner_space) u v <=>
    is_inner_space (s,inprod) /\ u IN s /\ v IN s ==> inprod u v = Cx(&0)`;;

let ARE_ORTHOGONAL = inner_space_prove
  (`!u v. u IN s /\ v IN s ==>
      (are_orthogonal (s,inprod) u v <=> inprod u v = Cx(&0)):`,
  MESON_TAC [are_orthogonal]);;

let ARE_ORTHOGONAL_SYM = inner_space_prove
  (`!u v. u IN s /\ v IN s
      ==> (are_orthogonal (s,inprod) u v <=> are_orthogonal (s,inprod) v u):`,
  SIMP_TAC[ARE_ORTHOGONAL] THEN REPEAT (STRIP_TAC ORELSE EQ_TAC)
  THEN ONCE_REWRITE_TAC[GSYM CNJ_INJ] THEN ASM_MESON_TAC[CNJ_CX;INPROD_CNJ]);;

let ARE_ORTHOGONAL_LSCALAR = inner_space_prove
  (`!u v. u IN s /\ v IN s /\ are_orthogonal (s,inprod) u v
      ==> !a. are_orthogonal (s,inprod) (a % u) v:`,
  IMP_REWRITE_TAC[are_orthogonal;INPROD_LSMUL;COMPLEX_MUL_RZERO]);;

let ORTHOGONAL_SUM_NORM = inner_space_prove
  (`!u v. u IN s /\ v IN s /\ are_orthogonal (s,inprod) u v ==>
    inprod (u+v) (u+v) = inprod u u + inprod v v:`,
  IMP_REWRITE_TAC[are_orthogonal;INPROD_ADD_LDIST;INPROD_ADD_RDIST;
    CFUN_SUBSPACE_ADD;INNER_SPACE_IS_SUBSPACE]
  THEN ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0]
  THEN (CONV_TAC o DEPTH_CONV o CHANGED_CONV) COMPLEX_POLY_CONV
  THEN MESON_TAC[INPROD_CNJ;CNJ_CX]);;

let ORTHOGONAL_DECOMPOS_WRT_CFUN = inner_space_prove
  (`!u v. u IN s /\ v IN s ==>
      let proj_v = inprod v u / inprod v v in
      let orthogonal_component = u - proj_v % v in
      u = proj_v % v + orthogonal_component
      /\ are_orthogonal (s,inprod) v orthogonal_component:`,
  REWRITE_TAC[LET_DEFS;CFUN_SUB_ADD2;are_orthogonal]
  THEN IMP_REWRITE_TAC [INPROD_SUB_LDIST;INPROD_RSMUL;CFUN_SUBSPACE_SMUL;
    INNER_SPACE_IS_SUBSPACE]
  THEN REPEAT STRIP_TAC THEN Pa.ASM_CASES_TAC `v=cfun_zero:` THENL [
    IMP_REWRITE_TAC [CFUN_SMUL_RZERO;INPROD_LZERO;CFUN_SUBSPACE_ZERO;
    INNER_SPACE_IS_SUBSPACE];
    IMP_REWRITE_TAC [COMPLEX_DIV_RMUL;INPROD_ZERO_EQ]
  ] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let ORTHOGONAL_DECOMPOS_WRT_CFUN_DECOMPOSITION = inner_space_prove
  (`!u v. u IN s /\ v IN s ==>
      let proj_v = inprod v u / inprod v v in
      let orthogonal_component = u - proj_v % v in
      u = proj_v % v + orthogonal_component:`,
  REWRITE_TAC [LET_DEFS]
  THEN MESON_TAC[REWRITE_RULE [LET_DEFS] ORTHOGONAL_DECOMPOS_WRT_CFUN]);;

let ORTHOGONAL_DECOMPOS_WRT_CFUN_ORTHOGONAL = inner_space_prove
  (`!u v. u IN s /\ v IN s ==>
      are_orthogonal (s,inprod) v (u - (inprod v u / inprod v v) % v):`,
  REWRITE_TAC [LET_DEFS]
  THEN MESON_TAC[REWRITE_RULE [LET_DEFS] ORTHOGONAL_DECOMPOS_WRT_CFUN]);;

let SCHWARZ_INEQUALITY = inner_space_prove
  (`!x y. x IN s /\ y IN s
      ==> norm (inprod x y) pow 2
        <= real_of_complex (inprod x x) * real_of_complex (inprod y y):`,
   IMP_REWRITE_TAC [GSYM INPROD_SELF_NORM;INPROD_SELF_RE]
  THEN REWRITE_TAC[MATCH_MP (TAUT `(A ==> B) ==> ((A ==> C) <=> (A /\ B ==>
    C))`) (SPEC_ALL (REWRITE_RULE [LET_DEFS] ORTHOGONAL_DECOMPOS_WRT_CFUN))]
  THEN REPEAT STRIP_TAC
  THEN FIRST_X_ASSUM (wrap (CHANGED_TAC o GEN_REWRITE_TAC (PATH_CONV "rl" o
    ONCE_DEPTH_CONV)))
  THEN IMP_REWRITE_TAC [ORTHOGONAL_SUM_NORM;ARE_ORTHOGONAL_LSCALAR;
    CFUN_SUBSPACE_SUB;INPROD_RSMUL;CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE;
    INPROD_LSMUL]
  THEN REWRITE_TAC[complex_div;CNJ_MUL;CNJ_INV]
  THEN IMP_REWRITE_TAC [INPROD_SELF_NORM]
  THEN REWRITE_TAC[GSYM RE_MUL_CX]
  THEN IMP_REWRITE_TAC [REAL_OF_COMPLEX;INPROD_SELF_REAL]
  THEN IMP_REWRITE_TAC [INPROD_SELF_CNJ]
  THEN REWRITE_TAC[COMPLEX_ADD_RDISTRIB;
    Pa.COMPLEX_FIELD `((x*y)*(z*t)*u)*v = (x*z)*(u*t)*(v*y):`;
    ONCE_REWRITE_RULE[GSYM COMPLEX_NORM_CNJ] COMPLEX_MUL_CNJ]
  THEN CASES_REWRITE_TAC COMPLEX_MUL_RINV
  THENL [
    IMP_REWRITE_TAC [INPROD_CNJ]
    THEN REWRITE_TAC[RE_ADD;RE_CX;COMPLEX_MUL_RID;GSYM CX_POW;REAL_LE_ADDR]
    THEN IMP_REWRITE_TAC [GSYM REAL_OF_COMPLEX_RE;REAL_OF_COMPLEX_MUL;
      REAL_LE_MUL;INPROD_SELF_POS;INPROD_SELF_POS;CFUN_SUBSPACE_SUB;
      CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE ]
    THEN REAL_TAC THEN HINT_EXISTS_TAC
    THEN IMP_REWRITE_TAC
      [CFUN_SUBSPACE_SUB;CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE]
    THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN GCONV_TAC COMPLEX_POLY_CONV
    THEN POP_ASSUM MP_TAC THEN IMP_REWRITE_TAC [INPROD_ZERO_EQ]
    THEN SIMP_TAC[] THEN IMP_REWRITE_TAC [INPROD_RZERO]
    THEN REWRITE_TAC[COMPLEX_NORM_0;RE_CX] THEN ARITH_TAC
  ]);;

let SCHWARZ_INEQUALITY2 = inner_space_prove
  (`!x y. x IN s /\ y IN s
      ==> norm (inprod x y)
        <= sqrt (real_of_complex (inprod x x)) *
                        sqrt(real_of_complex (inprod y y)):`,
  TARGET_REWRITE_TAC[GSYM (GEN_ALL (Pa.SPEC `norm z:` POW_2_SQRT));GSYM SQRT_MUL]
   SQRT_MONO_LE_EQ THEN
  IMP_REWRITE_TAC[ SCHWARZ_INEQUALITY;
  INPROD_SELF_POS;NORM_POS_LE;REAL_LE_MUL;REAL_LE_POW_2]);;

let SCHWARZ_INEQUALITY_ENHANCED = inner_space_prove
  (`!x y. x IN s /\ y IN s ==>
      real_of_complex ((inprod x y - inprod y x) / (Cx(&2) * ii)) pow 2
        <= real_of_complex (inprod x x) * real_of_complex (inprod y y):`,
  IMP_REWRITE_TAC [MATCH_MP (MESON[REAL_LE_TRANS]
    `!f g. (P ==> f x y <= g x y) ==> P /\ z <= f x y ==> z <= g x y`)
    (SPEC_ALL SCHWARZ_INEQUALITY);
    MATCH_MP (REAL_ARITH `x=y+z ==> &0<=y /\ t=z ==> t<=x`) COMPLEX_SQNORM]
  THEN REWRITE_TAC[REAL_LE_POW_2]
  THEN IMP_REWRITE_TAC [MESON[] `(x:real) = y ==> x pow 2 = y pow 2`]
  THEN ONCE_REWRITE_TAC[GSYM CX_INJ]
  THEN REWRITE_TAC[CX_IM_CNJ;GSYM COMPLEX_INV_II;complex_div;COMPLEX_INV_MUL]
  THEN IMP_REWRITE_TAC [INPROD_CNJ;REAL_OF_COMPLEX]
  THEN REWRITE_TAC[SIMPLE_COMPLEX_ARITH `x*y*inv ii=inv ii*(x*y)`;
    COMPLEX_INV_II;GSYM complex_div]
  THEN MESON_TAC[INPROD_CNJ;CX_IM_CNJ;REAL_CX]);;


(* ------------------------------------------------------------------------- *)
(* OPERATORS                                                                 *)
(* ------------------------------------------------------------------------- *)

(* "cop" stands for "Complex-valued function OPerator" *)

new_type_abbrev ("cop",`:cfunB->cfun`);;
new_type_abbrev ("copB",`:cfunC->cfunB`);;
new_type_abbrev ("cops",`:cfun->cfun`);;

let cop_add = new_definition
  `cop_add:cop->cop->cop = fun_map2 (+)`;;

let cop_sub = new_definition
  `cop_sub:cop->cop->cop = fun_map2 (-)`;;

let cop_neg = new_definition
  `cop_neg:cop->cop = (o) (--)`;;

let cop_mul = new_definition
  `cop_mul:cop->copB->(cfunC->cfun) = (o)`;;

let cop_smul = new_definition
  `cop_smul:complex->cop->cop = (o) o (%)`;;

let cop_zero = new_definition
  `cop_zero:cop = K cfun_zero`;;

let cop_pow = define
  `cop_pow (op:cfun->cfun) 0 = I /\
  cop_pow op (SUC n) = cop_mul op (cop_pow op n)`;;

let cop_cnj = new_definition
  `cop_cnj:cop->cop = (o) cfun_cnj`;;

let cop_defs = CONJS
  [cop_add;cop_sub;cop_neg;cop_mul;cop_smul;cop_zero;I_THM;cop_pow;cop_cnj];;

let prioritize_cop () =
  overload_interface("+",`cop_add:cop->cop->cop`);
  overload_interface("-",`cop_sub:cop->cop->cop`);
  overload_interface("--",`cop_neg:cop->cop`);
  overload_interface("**",`cop_mul:cop->copB->(cfunC->cfun)`);
  overload_interface("pow",`cop_pow:(cfun->cfun)->num->(cfun->cfun)`);
  overload_interface("%",`cop_smul:complex->cop->cop`);;

prioritize_cop ();;

(* Intended restriction of FUN_EQ_THM to the type :cop *)
let COP_EQ = prove
  (`!f g:cop. f = g <=> (!x. f x = g x)`,
  REWRITE_TAC[FUN_EQ_THM]);;

let COP_TO_CFUN = CONJS [FUN_MAP_THMS;o_THM;cop_defs;COP_EQ];;

let COP_POW_CONV =
  let th = REWRITE_CONV[cop_pow;cop_mul;I_O_ID] `cop_pow t (SUC 0)` in
  fun t ->
    let (h,_) = strip_comb t in
    if name_of h = "cop_pow"
    then (CHANGED_CONV (RAND_CONV (REDEPTH_CONV num_CONV)
      THENC REWRITE_CONV[cop_pow;th])) t
    else failwith "COP_POW_CONV";;

let COP_ARITH_TAC =
  let lemma = MESON[] `(!x. P x <=> Q x) ==> (!x. P x) = (!x. Q x)` in
  CONV_TAC (TOP_DEPTH_CONV COP_POW_CONV)
  THEN REWRITE_TAC[COP_TO_CFUN]
  THEN (CFUN_ARITH_TAC
    ORELSE (REPEAT STRIP_TAC THEN CONV_TAC PRENEX_CONV
      THEN MATCH_MP_TAC lemma THEN CFUN_ARITH_TAC));;

let COP_ARITH t = prove(t,COP_ARITH_TAC);;

(* Properties *)
let COP_ZERO = COP_ARITH `!x. cop_zero x = cfun_zero`;;

let COP_SMUL = COP_ARITH `!a op. a % op = \x. a * op x`;;

let COP_SMUL_THM = COP_ARITH `!a op x. (a % op) x = a % op x`;;

let COP_SMUL_ALT = COP_ARITH `!a op. a % op = \x. a * op x`;;

let COP_MUL = COP_ARITH `!op1 op2. op1 ** op2 = \x. op1 (op2 x)`;;

let COP_MUL_THM = COP_ARITH `!op1 op2 x. (op1 ** op2) x = op1 (op2 x)`;;

let COP_ADD = COP_ARITH `!op1 op2. op1 + op2 = \x. op1 x + op2 x`;;

let COP_SUB_ABS = COP_ARITH `!op1 op2. op1 - op2 = \x. op1 x - op2 x`;;

let COP_ADD_THM = COP_ARITH `!op1 op2 x. (op1 + op2) x = op1 x + op2 x`;;

let COP_SUB_THM = COP_ARITH `!op1 op2 x. (op1 - op2) x = op1 x - op2 x`;;

let COP_ZERO_THM = COP_ARITH `cop_zero x = cfun_zero`;;

let COP_MUL_LID = COP_ARITH `!op. I ** op = op`;;

let COP_MUL_RID = COP_ARITH `!op. op ** I = op`;;

let COP_I_ID = CONJ COP_MUL_LID COP_MUL_RID;;

let COP_ENTIRE = COP_ARITH
  `!a x. a % x = cop_zero <=> a = Cx(&0) \/ x = cop_zero`;;

let COP_ZERO_NEQ_ID = prove
  (`~(I = cop_zero)`,
  REWRITE_TAC[COP_TO_CFUN;CFUN_TO_COMPLEX;NOT_FORALL_THM]
  THEN Pa.EXISTS_TAC `\x. Cx(&1):` THEN CONV_TAC COMPLEX_FIELD);;

let COP_SMUL_I_ZERO = prove
  (`!a. a % I = cop_zero <=> a = Cx(&0)`,
  REWRITE_TAC[COP_ENTIRE;COP_ZERO_NEQ_ID]);;

let COP_SMUL_I_ONE = prove
  (`!a. a % I = I <=> a = Cx(&1)`,
  REWRITE_TAC[COP_TO_CFUN;CFUN_TO_COMPLEX] THEN GEN_TAC THEN EQ_TAC
  THENL [DISCH_THEN (MP_TAC o Pa.SPEC `\x.Cx(&1):`); ALL_TAC]
  THEN CONV_TAC COMPLEX_FIELD);;

let COP_MUL_I_SYM = COP_ARITH `!op. op ** I = I ** op`;;

let COP_ADD_I_SYM = COP_ARITH `!op. op + I = I + op`;;

let COP_I_SCALAR = COP_ARITH `(\x. a % x)  = a % I`;;

let COP_SMUL = COP_ARITH `!a op. a % op = \x. a % op x`;;

let COP_MUL_THM = COP_ARITH `!x op1 op2. (op1 ** op2) x = op1 (op2 x)`;;

let COP_SMUL_LNEG = COP_ARITH `!a op. --a % op = --(a % op)`;;

let COP_SMUL_RNEG = COP_ARITH `!a op. a % --op = --(a % op)`;;

let COP_SUB = COP_ARITH `!op1 op2. op1 - op2 = op1 + --op2`;;

let COP_SUB_NEG = COP_ARITH `!op1 op2. op1 - op2 = op1 + --op2`;;

let COP_NEG_NEG = COP_ARITH `!op. --(--op) = op`;;

let COP_NEG_ADD = COP_ARITH `!op1 op2. --(op1 + op2) = --op1 + --op2`;;

let COP_NEG_SUB = COP_ARITH `!op1 op2. --(op1 - op2) = --op1 + op2`;;

let COP_NEG_CLAUSES = CONJS [COP_NEG_NEG;COP_NEG_ADD;COP_NEG_SUB;
  COP_SUB;COP_SUB_NEG];;

let COP_SMUL_ASSOC = COP_ARITH `!a b op. a % (b % op) = (a * b) % op`;;

let COP_SMUL_SYM = COP_ARITH `!a b op. a % (b % op) = b % (a % op)`;;

let COP_MUL_LSMUL = COP_ARITH `!op1 op2. a % op1 ** op2 = a % (op1 ** op2)`;;

let COP_ADD_SYM = COP_ARITH `!op1 op2. op1 + op2 = op2 + op1 `;;

let COP_ADD_ASSOC = COP_ARITH
  `!op1 op2 op3. (op1 + op2) + op3  = op1 + op2 + op3 `;;

let COP_ADD_LDISTRIB = COP_ARITH
  `!a op1 op2. a % (op1 + op2) = a % op1 + a % op2`;;

let COP_ADD_RDISTRIB = COP_ARITH `!a b op. (a + b) % op = a % op + b % op`;;

let COP_SMUL_INV_ID = COP_ARITH
  `!a op. ~(a = Cx (&0)) ==> a % (inv a % op) = op`;;

let COP_SUB_LDISTRIB = COP_ARITH `!a x y. a % (x - y) = a % x - a % y`;;

let COP_SUB_RADD = COP_ARITH `!x y z. x - (y + z) = x - y - z`;;

let COP_ADD_RSUB = COP_ARITH `!x y z. x + (y - z) = (x + y) - z`;;

let COP_SUB_SUB = COP_ARITH `!x y z. x - (y - z) = x - y + z`;;

let COP_ADD_RID = COP_ARITH `!x. x + cop_zero = x`;;

let COP_ADD_LID = COP_ARITH `!x. cop_zero + x = x`;;

let COP_ADD_SYM = COP_ARITH `!op1 op2. op1 + op2 = op2 + op1`;;

let COP_ADD_ASSOC = COP_ARITH `!x y z. (x + y) + z = x + y + z`;;

let COP_ADD_AC = COP_ARITH
  `!m n p. m + n = n + m /\ (m + n) + p = m + n + p /\ m + n + p = n + m + p`;;

let COP_MUL_ASSOC = COP_ARITH `!x y z . (x ** y) ** z = x ** y ** z`;;

let COP_SUB_REFL = COP_ARITH `!x. x - x = cop_zero`;;

let COP_SUB_ADD = COP_ARITH `!x y z. (x-y)+z= (x+z)-y`;;

let COP_NEG_INJ = COP_ARITH `!x y. --x = --y <=> x = y`;;

let COP_EQ_ADD_LCANCEL = COP_ARITH `!x y z. x + y = x + z <=> y=z`;;

let COP_EQ_ADD_RCANCEL = COP_ARITH `!x y z. x + z = y + z <=> x=y`;;

let COP_EQ_SUB_LCANCEL = COP_ARITH `!x y z. x - y = x - z <=> y=z`;;

let COP_EQ_LSUB = COP_ARITH `!x y z. x - y = z <=> x = z + y`;;

let COP_EQ_RSUB = COP_ARITH `!x y z. x = y - z <=> x + z = y`;;

let COP_MUL_LZERO = COP_ARITH `!op. cop_zero ** op = cop_zero`;;

let COP_SUB_REFL = COP_ARITH `!op. op - op = cop_zero`;;

let COP_SMUL_LID_NEG = COP_ARITH `!x. (--Cx(&1)) % x = --x`;;

let COP_ADD_RID = COP_ARITH `!op. op + cop_zero = op`;;

let COP_ADD_LID = COP_ARITH `!op. cop_zero + op = op`;;

let COP_SMUL_LID = COP_ARITH `!op. Cx(&1) % op = op`;;

let COP_SMUL_RZERO = COP_ARITH `!op. a % cop_zero = cop_zero`;;

let COP_SUB_LZERO = COP_ARITH `!op. cop_zero - op = --op`;;

let COP_SUB_RZERO = COP_ARITH `!op. op - cop_zero  = op`;;

let COP_SMUL_LZERO = COP_ARITH `!x. Cx(&0) % x = cop_zero`;;

let COP_ZERO_CLAUSES = CONJS
  [COP_MUL_LZERO;COP_SUB_REFL;COP_ADD_RID;COP_ADD_LID;COP_SMUL_RZERO];;

let COP_ADD_MUL_RDISTRIB =
  COP_ARITH `!op1 op2 op3. (op1 + op2) ** op3 = op1 ** op3 + op2 ** op3`;;

let COP_SUB_MUL_RDISTRIB =
  COP_ARITH `!op1 op2 op3. (op1 - op2) ** op3 = op1 ** op3 - op2 ** op3`;;

let COP_EQ_LSUB_LSUB = COP_ARITH `!x y z. x - y = z <=> x - z = y`;;

let COP_EQ_LSMUL = COP_ARITH `!a x y. a % x = a % y <=> x = y \/ a = Cx(&0)`;;

let COP_EQ_MUL_LCANCEL2 = prove
  (`!x y z t:cop. ~(x=Cx(&0)) ==> (x % y = z % t <=> y = (z / x) % t)`,
  REWRITE_TAC[COP_TO_CFUN;CFUN_TO_COMPLEX] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC (MESON[]
    `(!x y. P x y <=> Q x y) ==> (!x y. P x y) = !x y. Q x y`)
  THEN REPEAT GEN_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

let COP_POW_2 = COP_ARITH `!op. op pow 2 = op ** op`;;

let COP_POW_I = prove
(`!n. I pow n = I`, INDUCT_TAC THEN ASM_SIMP_TAC[cop_pow;COP_MUL_LID]);;

let COP_POW_ZERO = prove(
 `!n. cop_zero pow  (n+1) = cop_zero`, INDUCT_TAC THEN
  ASM_MESON_TAC[cop_pow;ADD_CLAUSES;ADD1;COP_MUL_LZERO;COP_MUL_RID]);;

let COP_POW_COMMUTE_N = prove
 (`!op1 op2. op1 ** op2 = op2 ** op1 ==>
    !n. op1 ** op2 pow n = op2 pow n ** op1`,
        REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
        ASM_REWRITE_TAC[cop_pow; GSYM COP_MUL_ASSOC;COP_MUL_LID;COP_MUL_RID] THEN
        ASM_REWRITE_TAC[GSYM cop_pow;COP_MUL_ASSOC]);;

let COP_ADD_2 = COP_ARITH `!op. Cx(&2) % op  = op + op`;;


(* ------------------------------------------------------------------------- *)
(* LINEAR OPERATORS                                                          *)
(* ------------------------------------------------------------------------- *)

let is_linear_cop = new_definition
  `is_linear_cop (op:cop) <=>
    !x y. op (x + y) = op x + op y /\ !a. op (a % x) = a % (op x)`;;

let LINCOP_ADD = prove
  (`!x y op. is_linear_cop op ==> op (x + y) = op x + op y`,
  SIMP_TAC[is_linear_cop]);;

let LINCOP_SMUL = prove
  (`!a x op. is_linear_cop op ==> op (a % x) = a % op x`,
  SIMP_TAC[is_linear_cop]);;

let LINCOP_SUB = prove
  (`!x y op. is_linear_cop op ==> op (x - y) = op x - op y`,
  SIMP_TAC[is_linear_cop;CFUN_SUB_NEG;GSYM CFUN_SMUL_LID_NEG]);;

let LINCOP_MUL_RSMUL = prove
  (`!a op1 op2. is_linear_cop op2 ==> op2 ** (a % op1) = a % (op2 ** op1)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN]);;

let LINCOP_SMUL_CLAUSES = CONJS [LINCOP_MUL_RSMUL;COP_ADD_LDISTRIB;
  COP_SUB_LDISTRIB;COP_MUL_LSMUL;COP_MUL_ASSOC;COP_MUL_LID];;

let LINCOP_MUL_RMUL = prove
  (`!op1 op2. is_linear_cop op2 ==> op2 ** (a % op1) = a % (op2 ** op1)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN]);;

let LINCOP_ADD_MUL_LDISTRIB = prove
  (`!op1 op2 op3. is_linear_cop op3 ==>
      op3 ** (op1 + op2) = op3 ** op1 + op3 ** op2`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN]);;

let LINCOP_SUB_MUL_LDISTRIB = prove
  (`!op1 op2 op3. is_linear_cop op3 ==>
      op3 ** (op1 - op2) = op3 ** op1 - op3 ** op2`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN;LINCOP_SUB]);;

let LINCOP_MUL_DISTRIB_CLAUSES =
  CONJS[COP_ADD_MUL_RDISTRIB;COP_SUB_MUL_RDISTRIB;LINCOP_ADD_MUL_LDISTRIB;
    LINCOP_SUB_MUL_LDISTRIB];;

let LINCOP_CFUN_ZERO = prove
  (`!op. is_linear_cop op ==> op cfun_zero = cfun_zero`,
  MESON_TAC[is_linear_cop;CFUN_SMUL_LZERO]);;

let COP_POW_SMUL = prove
  (`!op. is_linear_cop op ==> !n a. (a % op) pow n = (a pow n) % (op pow n)`,
  REWRITE_TAC[is_linear_cop] THEN REPEAT (INDUCT_TAC ORELSE STRIP_TAC)
  THEN ASM_REWRITE_TAC[COP_TO_CFUN;complex_pow] THEN CFUN_ARITH_TAC);;

let COP_POW_SMUL2 = prove
  (`!op n a. is_linear_cop op ==>  (a % op) pow n = (a pow n) % (op pow n)`,
  MESON_TAC[COP_POW_SMUL]);;


(* Congruence properties *)

let ADD_LINCOP = prove
  (`!op1 op2.
    is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 + op2)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
  THEN COP_ARITH_TAC);;

let SUB_LINCOP = prove
  (`!op1 op2.
    is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 - op2)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
  THEN COP_ARITH_TAC);;

let SMUL_LINCOP = prove
  (`!a op. is_linear_cop op ==> is_linear_cop (a % op)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
  THEN COP_ARITH_TAC);;

let MUL_LINCOP = prove
  (`!op1 op2.
    is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 ** op2)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
  THEN COP_ARITH_TAC);;

let ARITH_LINCOP_CLAUSES = CONJS
  [ADD_LINCOP;SUB_LINCOP;SMUL_LINCOP;MUL_LINCOP];;

let linearity_thms = ref [];;
let add_linearity_thm thm =
  let thm = GIMP_IMP thm in
  linearity_thms := thm :: !linearity_thms;
  let eta_thm = SIMP_RULE[ETA_AX] thm in
  if (not (equals_thm thm eta_thm))
  then linearity_thms := eta_thm :: !linearity_thms;;
let add_linearity_thms = List.iter add_linearity_thm;;

add_linearity_thms [ADD_LINCOP;SUB_LINCOP;SMUL_LINCOP;MUL_LINCOP;
  REWRITE_RULE[cop_smul] SMUL_LINCOP];;

let I_LINCOP = prove
  (`is_linear_cop I`,
  REWRITE_TAC[is_linear_cop;I_DEF]);;

let COP_POW_SCALAR = prove
(`!a n. (\x. a % x) pow n = (\x. (a pow n) % x)`,
 SIMP_TAC[COP_ARITH `(\x. a % x)  = a % I`;COP_POW_SMUL;I_LINCOP;COP_POW_I]);;

add_linearity_thms [I_LINCOP;REWRITE_RULE[I_DEF] I_LINCOP];;

let ZERO_LINCOP = prove
  (`is_linear_cop cop_zero`,
  REWRITE_TAC[is_linear_cop;COP_ZERO_THM] THEN COP_ARITH_TAC);;

add_linearity_thms [ZERO_LINCOP];;

let SCALAR_LINCOP = prove
  (`!a. is_linear_cop \x. a % x`,
  REWRITE_TAC[is_linear_cop] THEN CFUN_ARITH_TAC);;

let POW_LINCOP = prove
  (`!op. is_linear_cop op ==> !n. is_linear_cop (op pow n)`,
  REPEAT (INDUCT_TAC ORELSE STRIP_TAC) THEN
  ASM_SIMP_TAC[cop_pow;I_LINCOP;MUL_LINCOP]);;

add_linearity_thms [SCALAR_LINCOP;POW_LINCOP];;

let LINEARITY_TAC g =
  let MATCH_MP_TAC x y = MATCH_MP_TAC x y in
  let TRY_LINEARITY_THM = ASM (MAP_FIRST (fun x ->
    MATCH_ACCEPT_TAC x ORELSE MATCH_MP_TAC x)) !linearity_thms in
  let LOOP = TRY_LINEARITY_THM ORELSE (SIMP_TAC[ETA_AX] THEN TRY_LINEARITY_THM)
    ORELSE (ASM_SIMP_TAC[] THEN NO_TAC) in
  (REPEAT STRIP_TAC THEN CHANGED_TAC (REPEAT (LOOP THEN REPEAT CONJ_TAC))) g;;

let is_set_linear_cop = new_definition
  `is_set_linear_cop s (op:cop) <=>
    !x y. x IN s /\ y IN s ==> op (x + y) = op x + op y /\
                !a. op (a % x) = a % (op x)`;;

let LINCOP_SLINCOP = prove
 (`!s op. is_linear_cop op ==> is_set_linear_cop s op`,
  SIMP_TAC[is_linear_cop;is_set_linear_cop]);;

let SLINCOP_SMUL = prove(`!a x op s. x IN s /\
 is_set_linear_cop s op ==> op (a % x) = a % op x`,
  MESON_TAC[is_set_linear_cop]);;

let SLINCOP_ADD = prove
  (`!x y op s. is_set_linear_cop s op /\ x IN s /\ y IN s
   ==> op (x + y) = op x + op y`,
  SIMP_TAC[is_set_linear_cop]);;

let SLINCOP_SUB = prove
  (`!x y op s.  is_cfun_subspace s /\ is_set_linear_cop s op /\
  x IN s /\ y IN s
   ==> op (x - y) = op x - op y`,
  MESON_TAC[SLINCOP_SMUL;CFUN_SUBSPACE_SMUL
  ;SLINCOP_ADD;CFUN_SUB_NEG;GSYM CFUN_SMUL_LID_NEG]);;

let SLINCOP_CFUN_ZERO = prove
  (`!op s. is_set_linear_cop s op /\ is_cfun_subspace s ==>
    op cfun_zero = cfun_zero`,
  ONCE_REWRITE_TAC[GSYM (Pa.SPEC `cfun_zero:` CFUN_SMUL_LZERO)] THEN
  MESON_TAC[SLINCOP_SMUL;CFUN_SMUL_LZERO;CFUN_SUBSPACE_ZERO]);;



(* ------------------------------------------------------------------------- *)
(* DUAL SPACE                                                                *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("cfun_dual",`:cfun->complex`);;
new_type_abbrev("cfun_dualB",`:cfunB->complex`);;

(* Note that all the above operations still apply on the dual space since
 * `:cfun_dual` is an instance of `cfun` itself.
 *)

let cfun_dual = new_definition
  `cfun_dual (spc:cfun->bool) =
    { f:cfun->complex | is_linear_cop (cfun_of_complex o f) }`;;

(*
 *let cfun_topological_dual = new_definition
 *  `cfun_topological_dual spc =
 *    { f | f IN cfun_dual spc /\ !x. f continuous (within (:cfun)) }`;;
 *)

let cop_transpose = new_definition
  `cop_transpose (f:cop) :cfun_dual->cfun_dualB = \phi. phi o f`;;


(* ------------------------------------------------------------------------- *)
(* FREQUENTLY USED OPERATORS                                                 *)
(* ------------------------------------------------------------------------- *)

let commutator = new_definition
  `commutator (op1:cfun->cfun) op2 = op1 ** op2 - op2 ** op1`;;

make_overloadable "com" `:A->A->A`;;
parse_as_infix("com",(24,"left"));;
overload_interface("com",`commutator:cops->cops->cops`);;

let COMMUTATOR_NEG = prove
  (`!op1 op2. commutator op1 op2 = -- commutator op2 op1`,
  REWRITE_TAC[commutator] THEN COP_ARITH_TAC);;


let COMMUTATOR_COMPOSIT = prove
 (`!op1 op2 a b c d. is_linear_cop op1 /\ is_linear_cop op2 ==>
  commutator (a%op1+b%op2) (c%op1+d%op2) =
   (a*d)% commutator op1 op2 - (b*c)% commutator op1 op2`,
   SIMP_TAC[commutator;LINCOP_MUL_DISTRIB_CLAUSES;
   LINCOP_SMUL_CLAUSES;COP_SMUL_ASSOC;COP_SUB_RADD] THEN COP_ARITH_TAC);;

let COMMUTATOR_SMUL = GEN_ALL(
   REWRITE_RULE[COP_SMUL_LZERO;COMPLEX_MUL_LZERO;
   COP_SUB_RZERO;COP_ADD_RID;COP_ADD_LID]
  (SPEC_V (`b:`,`Cx(&0):`) (SPEC_V(`c:`,`Cx(&0):`) COMMUTATOR_COMPOSIT)));;

let COMMUTATOR_ZERO_SYM = prove
  (`!op1 op2. commutator op1 op2 = cop_zero <=> commutator op2 op1 = cop_zero`,
  REWRITE_TAC[commutator;COP_EQ_LSUB;COP_ADD_LID] THEN MESON_TAC[]);;

let COMMUTATOR_SCALAR = prove
  (`!op a. is_linear_cop op ==>
  commutator op (\x. a%x) = cop_zero`,
  SIMP_TAC[commutator;COP_SUB_ABS;COP_MUL;LINCOP_SMUL] THEN COP_ARITH_TAC);;

let COMMUTATOR_SCALAR_OP = prove
  (`!op a. is_linear_cop op ==>
  commutator op (a%op) = cop_zero`,
  SIMP_TAC[commutator;LINCOP_MUL_RSMUL] THEN COP_ARITH_TAC);;

let COMMUTATOR_ZERO = prove
  (`!op. is_linear_cop op ==>
  commutator op cop_zero = cop_zero`,
  SIMP_TAC[cop_zero;K_DEF;GSYM CFUN_SMUL_LZERO;commutator;
  COP_SUB_ABS;COP_MUL;LINCOP_SMUL] THEN COP_ARITH_TAC);;

let LINCOP_COMMUTATOR = prove
  (`!op1 op2. is_linear_cop op1 /\ is_linear_cop op2
    ==> is_linear_cop (commutator op1 op2)`,
  REWRITE_TAC[commutator] THEN REPEAT STRIP_TAC THEN LINEARITY_TAC);;

add_linearity_thm LINCOP_COMMUTATOR;;

let expectation = new_definition
  `expectation (inprod:inprod) f op = inprod f (op f)`;;

let deviation = new_definition
  `deviation (inprod:inprod) f op = op - (\x. expectation inprod f op % x)`;;

let DEVIATION_ALT = prove
  (`!inprod f op. deviation inprod f op = op - expectation inprod f op % I`,
  REWRITE_TAC[deviation] THEN COP_ARITH_TAC);;

let LINCOP_DEVIATION = prove
  (`!inprod state op. is_linear_cop op
    ==> is_linear_cop (deviation inprod state op)`,
    REWRITE_TAC[deviation;GSYM COP_SMUL] THEN LINEARITY_TAC);;

add_linearity_thm LINCOP_DEVIATION;;

let variance = new_definition
  `variance  (inprod:inprod) f op =
    expectation inprod f (deviation inprod f op ** deviation inprod f op)`;;

let DEVIATION_COMMUTATOR = prove
  (`!inprod op1 op2 state. is_linear_cop op1 /\ is_linear_cop op2
    ==> commutator (deviation inprod state op1) (deviation inprod state op2)
      = commutator op1 op2`,
  SIMP_TAC[DEVIATION_ALT;commutator] THEN
  IMP_REWRITE_TAC [LINCOP_SUB_MUL_LDISTRIB]
  THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN ASM_SIMP_TAC[LINCOP_MUL_DISTRIB_CLAUSES;COP_MUL_LSMUL;COP_I_ID;
    LINCOP_MUL_RMUL;MESON[COP_SMUL_SYM]
      `f (a % (b % op)) (b % (a % op)) = f (a % (b % op)) (a % (b % op))`]
  THEN COP_ARITH_TAC);;

let EXPEC_ZERO_STATE = prove
  (`!s inprod op. is_linear_cop op /\ is_inner_space (s,inprod)
    ==> expectation inprod cfun_zero op = Cx(&0)`,
  MESON_TAC[expectation;INPROD_ZERO;LINCOP_CFUN_ZERO]);;


(* ------------------------------------------------------------------------- *)
(* CLOSURE                                                                   *)
(* ------------------------------------------------------------------------- *)

let is_closed_by = new_definition
  `is_closed_by s f <=> !x. x IN s ==> f x IN s`;;

let IS_CLOSED_BY_THM = prove
 (`!x s f. is_closed_by s f /\ x IN s ==> f x IN s`,SIMP_TAC[is_closed_by]);;

let IS_CLOSED_BY_COMPOSE = prove
  (`!s f g. is_closed_by s f /\ is_closed_by s g ==> is_closed_by s (f o g)`,
  REWRITE_TAC[is_closed_by;o_DEF] THEN MESON_TAC[]);;

let IS_CLOSED_BY_I = prove
  (`!s. is_closed_by s I`,
  REWRITE_TAC[is_closed_by;I_THM]);;

let IS_CLOSED_BY_COP_ADD = prove
  (`!s op1 op2.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (op1+op2)`,
  REWRITE_TAC[is_closed_by;COP_TO_CFUN] THEN MESON_TAC[CFUN_SUBSPACE_ADD]);;

let IS_CLOSED_BY_COP_SUB = prove
  (`!s op1 op2.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (op1-op2)`,
  REWRITE_TAC[is_closed_by;COP_TO_CFUN] THEN MESON_TAC[CFUN_SUBSPACE_SUB]);;

let IS_CLOSED_BY_COP_MUL = prove
  (`!s op1 op2.
      is_closed_by s op1 /\ is_closed_by s op2 ==> is_closed_by s (op1**op2)`,
  REWRITE_TAC[is_closed_by;COP_TO_CFUN] THEN MESON_TAC[]);;

let IS_CLOSED_SCALAR = prove
  (`!s a. is_cfun_subspace s ==> is_closed_by s (a % I)`,
  SIMP_TAC[is_closed_by;is_cfun_subspace;COP_TO_CFUN]);;

let IS_CLOSED_INPROD_SCALAR = inner_space_prove
  (`!a. is_closed_by s (a % I):`,
  SIMP_TAC[is_closed_by;is_inner_space;IS_CLOSED_SCALAR]);;

let IS_CLOSED_BY_COP_SMUL = prove
  (`!s a op.
      is_cfun_subspace s /\ is_closed_by s op ==> is_closed_by s (a % op)`,
  IMP_REWRITE_TAC[is_closed_by;COP_TO_CFUN;CFUN_SUBSPACE_SMUL]);;

let IS_CLOSED_BY_COMMUTATOR = prove
  (`!s a op.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (commutator op1 op2)`,
  IMP_REWRITE_TAC[commutator;IS_CLOSED_BY_COP_MUL;IS_CLOSED_BY_COP_SUB]);;



(* ------------------------------------------------------------------------- *)
(* HERMITIAN                                                                 *)
(* ------------------------------------------------------------------------- *)

let is_hermitian = new_definition
  `is_hermitian ((s,inprod):inner_space) op1 op2 <=>
    is_inner_space (s,inprod) ==>
      is_closed_by s op1 /\ is_closed_by s op2
      /\ is_linear_cop op1 /\ is_linear_cop op2
      /\ !x y. x IN s /\ y IN s ==> inprod x (op1 y) = inprod (op2 x) y`;;

let HERM_LINCOP = full_inner_space_prove
  (`!op1 op2. is_hermitian is op1 op2 ==> is_linear_cop op1
                /\ is_linear_cop op2:`,
  SIMP_TAC[FORALL_INNER_SPACE_THM;is_hermitian]);;

let HERM_LINCOP_L = full_inner_space_prove
  (`!op1 op2. is_hermitian is op1 op2 ==> is_linear_cop op1:`,
  SIMP_TAC[FORALL_INNER_SPACE_THM;is_hermitian]);;

let HERM_LINCOP_R = full_inner_space_prove
  (`!op1 op2. is_hermitian is op1 op2 ==> is_linear_cop op2:`,
  SIMP_TAC[FORALL_INNER_SPACE_THM;is_hermitian]);;

let HERM_IS_CLOSED_BY_L = inner_space_prove
  (`!op1 op2. is_hermitian (s,inprod) op1 op2 ==> is_closed_by s op1:`,
  SIMP_TAC[is_hermitian]);;

let HERM_IS_CLOSED_BY_R = inner_space_prove
  (`!op1 op2. is_hermitian (s,inprod) op1 op2 ==> is_closed_by s op2:`,
  SIMP_TAC[is_hermitian]);;


let HERM_ITSELF = inner_space_prove
  (`!op1 op2 x y. is_hermitian (s,inprod) op1 op2 /\ x IN s /\ y IN s ==>
   inprod x (op1 y) = inprod (op2 x) y:`,
  SIMP_TAC[is_hermitian]);;

let ADD_HERM = full_inner_space_prove
  (`!op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
    ==> is_hermitian is (op1+op3) (op2+op4):`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN IMP_REWRITE_TAC [COP_TO_CFUN;CFUN_SUBSPACE_ADD;INNER_SPACE_IS_SUBSPACE;
    INPROD_ADD_LDIST;INPROD_ADD_RDIST]);;

let SUB_HERM = full_inner_space_prove
  (`!op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
      ==> is_hermitian is (op1-op3) (op2-op4):`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN IMP_REWRITE_TAC [COP_TO_CFUN;CFUN_SUBSPACE_SUB;INNER_SPACE_IS_SUBSPACE;
    INPROD_SUB_LDIST;INPROD_SUB_RDIST]);;

let MUL_HERM = full_inner_space_prove
  (`!op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
      ==> is_hermitian is (op1**op3) (op4**op2):`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN REWRITE_TAC[COP_TO_CFUN;cop_mul;o_DEF] THEN ASM_MESON_TAC[]);;

let SMUL_HERM = full_inner_space_prove
  (`!a op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
      ==> is_hermitian is (a % op1) (cnj a % op2):`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN IMP_REWRITE_TAC [COP_TO_CFUN;CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE;
    INPROD_LSMUL;INPROD_RSMUL]
  THEN ASM_MESON_TAC[CNJ_CNJ]);;

let HERMITAIN_INPROD = inner_space_prove
  (`!op1 op2 op3. is_hermitian (s,inprod) op1 op2 /\ is_closed_by s op3
    ==> !x y. x IN s /\ y IN s
      ==> inprod x ((op1 ** op3) y) = inprod (op2 x) (op3 y):`,
   MESON_TAC[HERM_ITSELF;COP_MUL;is_closed_by]);;

let ZERO_HERM = prove
  (`!is. is_hermitian is cop_zero cop_zero`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian] THEN
  IMP_REWRITE_TAC[is_closed_by;ZERO_LINCOP;
    COP_ZERO_THM;CFUN_SUBSPACE_ZERO;INNER_SPACE_IS_SUBSPACE;INPROD_RZERO;
    INPROD_LZERO]);;

let ARITH_HERM_CLAUSES = CONJS [ADD_HERM;SUB_HERM;MUL_HERM;SMUL_HERM];;

let HERM_SYM = prove
  (`!is op1 op2.
    is_hermitian is op1 op2 <=> is_hermitian is op2 op1`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN MESON_TAC[CX_INJ;INPROD_CNJ]);;

let HERM_UNIQUENESS = prove
  (`!s inprod op1 op2 op3.
      is_inner_space (s,inprod)
      /\ is_hermitian (s,inprod) op1 op2 /\ is_hermitian (s,inprod) op1 op3
        ==> !x. x IN s ==> op2 x = op3 x`,
  IMP_REWRITE_TAC [is_hermitian;COP_EQ;is_closed_by;GSYM INPROD_INJ_ALT]
  THEN ASM_MESON_TAC[]);;

let HERM_UNIQUENESS_ALT = prove
  (`!s inprod op1 op2 op3.
    is_inner_space (s,inprod) /\
    is_hermitian (s,inprod) op2 op1 /\ is_hermitian (s,inprod) op3 op1
      ==> !x. x IN s ==> op2 x = op3 x`,
  MESON_TAC[HERM_SYM;HERM_UNIQUENESS]);;

let HERM_PROP_ADVANCED = inner_space_prove
  (`!a b op1 op2 op3 op4 op5.
    is_hermitian (s,inprod) op1 op2 /\ is_hermitian (s,inprod) op3 op4
    /\ is_hermitian (s,inprod) op5 (a % op1 + b % op3)
      ==> !x. x IN s ==> op5 x = (cnj a % op2 + cnj b % op4) x:`,
  IMP_REWRITE_TAC[COP_EQ;GIMP_IMP HERM_UNIQUENESS_ALT]
  THEN MESON_TAC[ARITH_HERM_CLAUSES;CNJ_CNJ;HERM_SYM]);;


(* ------------------------------------------------------------------------- *)
(* SELF ADJOINT                                                              *)
(* ------------------------------------------------------------------------- *)

let is_self_adjoint = new_definition
  `is_self_adjoint is op <=> is_hermitian is op op`;;

let IS_SELF_ADJOINT =
  REWRITE_RULE[FORALL_INNER_SPACE_THM;is_hermitian] is_self_adjoint;;

let SELF_ADJ_IS_LINCOP = full_inner_space_prove
  (`!op. is_self_adjoint is op ==> is_linear_cop op:`,
  IMP_REWRITE_TAC[is_self_adjoint;HERM_LINCOP_L]);;

let SELF_ADJ_IS_CLOSED_BY = inner_space_prove
  (`!op. is_self_adjoint (s,inprod) op ==> is_closed_by s op:`,
  IMP_REWRITE_TAC[is_self_adjoint;HERM_IS_CLOSED_BY_L]);;

let SELF_ADJ_INPROD = inner_space_prove
  (`!op1 op2. is_self_adjoint (s,inprod) op1 /\ is_closed_by s op2
    ==> !x y. x IN s /\ y IN s
      ==> inprod x ((op1 ** op2) y) = inprod (op1 x) (op2 y):`,
  REWRITE_TAC[IS_SELF_ADJOINT;COP_MUL;is_closed_by] THEN MESON_TAC[]);;

let ADD_SELF_ADJ = full_inner_space_prove
  (`!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (op1 + op2):`,
  IMP_REWRITE_TAC[is_self_adjoint;ADD_HERM]);;

let SUB_SELF_ADJ = full_inner_space_prove
  (`!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (op1 - op2):`,
  IMP_REWRITE_TAC[is_self_adjoint;SUB_HERM]);;

let SMUL_SELF_ADJ = full_inner_space_prove
  (`!a op. real a /\ is_self_adjoint is op ==> is_self_adjoint is (a % op):`,
  MESON_TAC[is_self_adjoint;SMUL_HERM;REAL_CNJ]);;

let MUL_SELF_ADJ = full_inner_space_prove
  (`!op1 op2.
    is_self_adjoint is op1 /\ is_self_adjoint is op2 /\ op1 ** op2 = op2 ** op1
    ==> is_self_adjoint is (op1 ** op2):`,
  MESON_TAC[is_self_adjoint;MUL_HERM]);;

let I_SELF_ADJ = prove
  (`!is. is_self_adjoint is I`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;IS_SELF_ADJOINT;I_LINCOP;I_THM;
    IS_CLOSED_BY_I]);;

let ZERO_SELF_ADJ = prove
  (`!is. is_self_adjoint is cop_zero`,
  REWRITE_TAC[is_self_adjoint;ZERO_HERM]);;

let selfadjoint_thms = ref [];;
let add_selfadjoint_thm thm =
  let thm = GIMP_IMP thm in
  selfadjoint_thms := thm :: !selfadjoint_thms;
  let eta_thm = SIMP_RULE[ETA_AX] thm in
  if (not (equals_thm thm eta_thm))
  then selfadjoint_thms := eta_thm :: !selfadjoint_thms;;
let add_selfadjoint_thms = List.iter add_selfadjoint_thm;;

let rec SELF_ADJOINT_TAC g =
  let MATCH_MP_TAC x y = MATCH_MP_TAC x y in
  let TRY_SELFADJOINT_THM =
    ASM (MAP_FIRST (fun x ->
      MATCH_ACCEPT_TAC x ORELSE MATCH_MP_TAC x)) !selfadjoint_thms in
  let LOOP =
    TRY_SELFADJOINT_THM ORELSE (SIMP_TAC[ETA_AX] THEN TRY_SELFADJOINT_THM)
    ORELSE (ASM_SIMP_TAC[] THEN NO_TAC) ORELSE LINEARITY_TAC
    ORELSE REAL_TAC ~alternatives:[SELF_ADJOINT_TAC;LINEARITY_TAC] in
  (REPEAT STRIP_TAC
  THEN (fun (_,c as g) ->
    let head = fst (strip_comb c) in
    if (name_of head = "is_self_adjoint"
      && can (type_match `:inner_space->cop->bool` (type_of head)) [])
    then CHANGED_TAC (REPEAT (LOOP THEN REPEAT CONJ_TAC)) g
    else FAIL_TAC "bad goal" g)) g;;

let REAL_TAC ?(alternatives=[]) =
  REAL_TAC ~alternatives:(SELF_ADJOINT_TAC::LINEARITY_TAC::alternatives);;

add_selfadjoint_thms [ADD_SELF_ADJ;SUB_SELF_ADJ;SMUL_SELF_ADJ;
  REWRITE_RULE[COP_SMUL] SMUL_SELF_ADJ;MUL_SELF_ADJ;I_SELF_ADJ;ZERO_SELF_ADJ];;

let ANTI_COMMUTATOR_SELF_ADJ = full_inner_space_prove
  (`!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (op1 ** op2 + op2 ** op1):`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;IS_SELF_ADJOINT]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN ASM IMP_REWRITE_TAC[IS_CLOSED_BY_COP_ADD;IS_CLOSED_BY_COP_MUL;COP_MUL;
    COP_ADD;IS_CLOSED_BY_COP_MUL;INNER_SPACE_IS_SUBSPACE;INPROD_ADD_LDIST;
    INPROD_ADD_RDIST]
  THEN ASM_MESON_TAC[COMPLEX_ADD_SYM;is_closed_by]);;

add_selfadjoint_thm ANTI_COMMUTATOR_SELF_ADJ;;

let NEG_SELF_ADJ = full_inner_space_prove
  (`!op. is_linear_cop op /\ is_self_adjoint is op
    ==> is_self_adjoint is (--op):`,
  ONCE_REWRITE_TAC[GSYM COP_SUB_LZERO] THEN SELF_ADJOINT_TAC);;

add_selfadjoint_thm NEG_SELF_ADJ;;

let SCALAR_II_HERM = inner_space_prove
  (`!op. is_linear_cop op /\ (!x y. inprod (op x) y = -- (inprod x (op y)))
      /\ is_closed_by s op
        ==> is_self_adjoint (s,inprod) (ii % op):`,
  IMP_REWRITE_TAC[IS_SELF_ADJOINT;COP_SMUL_THM;IS_CLOSED_BY_COP_SMUL;
   is_closed_by;INNER_SPACE_IS_SUBSPACE;INPROD_LSMUL;INPROD_RSMUL;
   CNJ_II;COMPLEX_NEG_MUL2] THEN LINEARITY_TAC);;

add_selfadjoint_thm SCALAR_II_HERM;;

let COMMUTATOR_ANTI_HERM = inner_space_prove
  (`!op1 op2. is_self_adjoint (s,inprod) op1 /\ is_self_adjoint (s,inprod) op2
    ==> !x y. x IN s /\ y IN s
     ==> inprod (commutator op1 op2 x) y = --(inprod x (commutator op1 op2 y)):`,
  IMP_REWRITE_TAC[commutator;IS_SELF_ADJOINT;COP_MUL_THM;COP_SUB_THM;
  is_closed_by;INPROD_SUB_LDIST;INPROD_SUB_RDIST;COMPLEX_NEG_SUB]);;

add_selfadjoint_thm COMMUTATOR_ANTI_HERM;;

let II_COMMUTATOR_HERM = full_inner_space_prove
  (`!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (ii % commutator op1 op2):`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;IS_SELF_ADJOINT] THEN
  IMP_REWRITE_TAC[COP_SMUL_THM;INPROD_RSMUL;
    INPROD_LSMUL;IS_CLOSED_BY_COMMUTATOR;IS_CLOSED_BY_COP_SMUL;CNJ_II;II_NZ;
    INNER_SPACE_IS_SUBSPACE;COMPLEX_MUL_LNEG;GSYM COMPLEX_MUL_RNEG;
    COMPLEX_EQ_MUL_LCANCEL;]
  THEN ONCE_REWRITE_TAC[COMPLEX_FIELD `x = --y <=> y = --x:complex`]
  THEN IMP_REWRITE_TAC [GIMP_IMP COMMUTATOR_ANTI_HERM;is_self_adjoint;
  is_hermitian;REWRITE_RULE[is_closed_by] IS_CLOSED_BY_COMMUTATOR;
  INNER_SPACE_IS_SUBSPACE;is_closed_by] THEN LINEARITY_TAC);;

add_selfadjoint_thm II_COMMUTATOR_HERM;;

let EXPEC_HERM_REAL = inner_space_prove
  (`!op state. is_self_adjoint (s,inprod) op /\ state IN s
    ==> real (expectation inprod state op):`,
  IMP_REWRITE_TAC[IS_SELF_ADJOINT;expectation;is_closed_by
  ;REAL_CNJ;INPROD_CNJ]);;

add_real_thms [EXPEC_HERM_REAL; REWRITE_RULE[expectation] EXPEC_HERM_REAL];;

let DEVIATION_HERM = inner_space_prove
  (`!op state. is_self_adjoint (s,inprod) op /\ state IN s
    ==> is_self_adjoint (s,inprod) (deviation inprod state op):`,
  REWRITE_TAC[DEVIATION_ALT] THEN SELF_ADJOINT_TAC THEN ASM_MESON_TAC[]);;

add_selfadjoint_thms [DEVIATION_HERM; REWRITE_RULE[deviation] DEVIATION_HERM];;

let VARIANCE_REAL = inner_space_prove
  (`!op state.  state IN s /\ is_self_adjoint (s,inprod) op
    ==> real (variance inprod state op):`,
  REWRITE_TAC[variance] THEN REAL_TAC THEN HINT_EXISTS_TAC
  THEN SELF_ADJOINT_TAC);;

add_real_thm VARIANCE_REAL;;


(* ------------------------------------------------------------------------- *)
(* EIGEN VALUES AND VECTORS                                                  *)
(* ------------------------------------------------------------------------- *)

let is_eigen_pair = new_definition
  `is_eigen_pair (op:cfun->cfun) (x,a) <=>
    is_linear_cop op ==> op x = a % x /\ ~(x = cfun_zero)`;;

let EIGEN_PAIR_SMUL = prove
  (`!op v x. is_eigen_pair op (x,v)
    ==> !a. ~(a = Cx(&0)) ==> is_eigen_pair op (a % x,v)`,
  SIMP_TAC[is_eigen_pair;CFUN_ENTIRE;LINCOP_SMUL;CFUN_SMUL_SYM]);;

let EIGEN_PAIR_ADD = prove
  (`!op v x y. is_eigen_pair op (x,v) /\ is_eigen_pair op (y,v)
        /\ ~(x + y = cfun_zero)
          ==> is_eigen_pair op (x+y,v)`,
  SIMP_TAC[is_eigen_pair;LINCOP_ADD;CFUN_ADD_LDISTRIB]);;

let EIGEN_SPACE_THM = prove
  (`!op. is_linear_cop op ==>
    !a. is_cfun_subspace ({ x | is_eigen_pair op (x,a) } UNION { cfun_zero })`,
  SIMP_TAC[is_cfun_subspace;IN_ELIM_THM;IN_UNION;IN_SING;CFUN_ENTIRE]
  THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CFUN_ADD_RID;CFUN_ADD_LID]
  THEN ASM_MESON_TAC[EIGEN_PAIR_SMUL;EIGEN_PAIR_ADD]);;

let is_eigen_val = new_definition
  `is_eigen_val (op:cfun->cfun) a <=> ?x. is_eigen_pair op (x,a)`;;

let is_eigen_fun = new_definition
  `is_eigen_fun (op:cfun->cfun) x <=> ?a. is_eigen_pair op (x,a)`;;

(* ------------------------------------------------------------------------- *)
(*                              cfun norm                                    *)
(* ------------------------------------------------------------------------- *)

let cfun_norm = new_definition
 `cfun_norm inprod (x:cfun) =  sqrt(real_of_complex (inprod x x))`;;

let INPROD_SUB_SELF = inner_space_prove(
  `!x y. x IN s /\ y IN s
     ==> real_of_complex (inprod (x-y) (x-y)) = real_of_complex(inprod x x) +
            real_of_complex(inprod y y) - &2*Re(inprod y x):`,
  IMP_REWRITE_TAC[INNER_SPACE_SUB;INPROD_SUB_LDIST;INPROD_SUB_RDIST;
  COMPLEX_FIELD  `x:complex - y - (z - h) = x + h - (z+y)`;INPROD_ADD_CNJ]
  THEN IMP_REWRITE_TAC[REAL_OF_COMPLEX_ADD;REAL_OF_COMPLEX_CX;
  REAL_OF_COMPLEX_SUB;INPROD_SELF_REAL;REAL_CX;REAL_SUB]);;

let INPROD_ADD_SELF = inner_space_prove(
  `!x y. x IN s /\ y IN s
     ==> real_of_complex (inprod (x+y) (x+y)) = real_of_complex(inprod x x) +
            real_of_complex(inprod y y) + &2*Re(inprod x y):`,
  IMP_REWRITE_TAC[INNER_SPACE_ADD
  ;INPROD_ADD_LDIST;INPROD_ADD_RDIST;
  COMPLEX_FIELD  `((x:complex) + y) + z + h = x + h + (y+z)`;INPROD_ADD_CNJ]
  THEN IMP_REWRITE_TAC[REAL_OF_COMPLEX_ADD;REAL_OF_COMPLEX_CX;
  INPROD_SELF_REAL;REAL_CX;REAL_ADD]);;

let INPROD_TRIANGLE_INEQ = inner_space_prove(
  `!x y. x IN s /\ y IN s
    ==> real_of_complex(inprod (x+y) (x+y)) <=
          (sqrt(real_of_complex (inprod x x)) +
          sqrt(real_of_complex (inprod y y))) pow 2:`,
  REWRITE_TAC[REAL_POW_2] THEN
  SIMP_TAC[REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_MUL_SYM;GSYM REAL_ADD_ASSOC;
  REAL_ARITH `x*x+x*y+x*y+y*y = x pow 2 + y pow 2 + &2*x*y`] THEN
  IMP_REWRITE_TAC[SQRT_POW_2;INPROD_SELF_POS] THEN
  IMP_REWRITE_TAC[INPROD_ADD_SELF;REAL_ADD_ASSOC;REAL_LE_LADD_IMP;
  REAL_LE_LMUL_EQ] THEN
  MESON_TAC[GEN_ALL (Pa.SPEC `Re z:` REAL_ABS_LE);COMPLEX_NORM_GE_RE_IM;
  REAL_INT_LT_CONV  `&0 < &2`;SCHWARZ_INEQUALITY2;REAL_LE_TRANS]);;

let INPROD_TRIANGLE_INEQ2 = inner_space_prove(
  `!x y. x IN s /\ y IN s
    ==> sqrt (real_of_complex(inprod (x+y) (x+y))) <=
          sqrt(real_of_complex (inprod x x)) +
          sqrt(real_of_complex (inprod y y)):`,
  let REAL_MANOP =  GEN_ALL(Pa.SPECL[`sqrt x:`;`sqrt y + sqrt z:`]
  (GEN_ALL(REAL_ARITH `&0 <= x /\ &0<= y ==> ( x <= y <=> abs x <= abs y)`))) in
   IMP_REWRITE_TAC[REAL_MANOP;REAL_LE_SQUARE_ABS;SQRT_POW_2;INPROD_TRIANGLE_INEQ;
   INPROD_SELF_POS;SQRT_POS_LE;INNER_SPACE_ADD;REAL_LE_ADD]);;

let CFUN_NORM_SUB = inner_space_prove(
  `!x y. x IN s /\ y IN s
     ==> cfun_norm inprod (x-y) = cfun_norm inprod (y-x):`,
   IMP_REWRITE_TAC[cfun_norm;INPROD_SUB_SELF] THEN
   ONCE_REWRITE_TAC[GSYM (Pa.SPEC `&2 *Re r:` RE_CX)] THEN
   IMP_REWRITE_TAC[GSYM INPROD_ADD_CNJ] THEN
   ONCE_SIMP_TAC[COMPLEX_ADD_SYM] THEN
   REWRITE_TAC[REAL_ARITH `(x:real)+y-z = y+x-z`]);;

let CFUN_NORM_SUB_INEQ = inner_space_prove(
  `!x y. x IN s /\ y IN s
     ==> cfun_norm inprod x - cfun_norm inprod y <= cfun_norm inprod (x-y):`,
   let arrange =  MESON[CFUN_ARITH `x = (x:cfun) - y + y`]
    `cfun_norm inprod x - cfun_norm inprod y =
        cfun_norm inprod (x-y+y) - cfun_norm inprod y` in
    ONCE_REWRITE_TAC[arrange] THEN
        IMP_REWRITE_TAC[INPROD_TRIANGLE_INEQ2;REAL_LE_SUB_RADD;cfun_norm;
        INNER_SPACE_SUB]);;
let cfun_dist = new_definition
 `cfun_dist (inprod:inprod) (x:cfun) (y:cfun) =
    sqrt (real_of_complex(inprod (x-y) (x-y)))`;;

let CFUN_DIST_TRIANGLE_ADD = inner_space_prove(
  `!x y x' y'. x IN s /\ y IN s /\ x' IN s /\ y' IN s
     ==> cfun_dist inprod (x+y) (x'+y')
           <= cfun_dist inprod x x' + cfun_dist inprod y y':`,
   IMP_REWRITE_TAC[cfun_dist;CFUN_ARITH `((x:cfun)+y)-(x'+y') = x-x'+y-y'`;
   INPROD_TRIANGLE_INEQ2;INNER_SPACE_SUB;INPROD_SELF_POS;SQRT_POS_LE;
   SQRT_MONO_LE;REAL_ABS_REFL;SQRT_POW_2;POW_2_SQRT]);;

let CFUN_DIST_REFL =  inner_space_prove(
 `!x. cfun_dist inprod x x = &0:`,
 REWRITE_TAC[cfun_dist;CFUN_SUB_REFL] THEN
 MESON_TAC[INPROD_ZERO;SQRT_0;REAL_OF_COMPLEX_CX]);;
let CFUN_NORM_0 = inner_space_prove(
  `cfun_norm inprod cfun_zero = &0:`,
  MESON_TAC[cfun_norm;INPROD_ZERO;REAL_OF_COMPLEX_CX;SQRT_0]);;

let CFUN_NORM_EQ_0 = inner_space_prove(
  `!x. x IN s ==> (cfun_norm inprod x = &0 <=> x = cfun_zero):`,
   MESON_TAC[cfun_norm;SQRT_EQ_0;REAL_OF_COMPLEX_ZERO;
   INPROD_ZERO_EQ;INPROD_NORM]);;

let CFUN_NORM_POS_LE = inner_space_prove(
  `!x. x IN s ==> &0 <= cfun_norm inprod x :`,
  MESON_TAC[cfun_norm;SQRT_POS_LE;INPROD_SELF_POS]);;

let CFUN_NORM_POW2 = inner_space_prove(
  `!x. x IN s ==> cfun_norm inprod x pow 2 = real_of_complex (inprod x x):`,
  MESON_TAC[cfun_norm;SQRT_POW_2;INPROD_SELF_POS]);;

let CFUN_NORM_INPROD_0 = inner_space_prove(
  `!x. x IN s ==> (cfun_norm inprod x = &0 <=>
                   real_of_complex(inprod x x) = &0):`,
   MESON_TAC[cfun_norm;INPROD_SELF_POS;SQRT_EQ_0]);;

let CFUN_NORM_NZ = inner_space_prove(
  `!x. x IN s ==> (~(x = cfun_zero) <=> &0 < cfun_norm inprod x):`,
   IMP_REWRITE_TAC[ GSYM CFUN_NORM_EQ_0] THEN
   MESON_TAC[REAL_ARITH ` y <= x ==>  (~(x=y) <=> y < x)`;CFUN_NORM_POS_LE]
   );;

let CFUN_NORM_SMUL = inner_space_prove(
  `!x a. x IN s ==> cfun_norm inprod (a%x) =  norm a * cfun_norm inprod x:`,
  IMP_REWRITE_TAC[cfun_norm;INPROD_RSMUL;INPROD_LSMUL;INNER_SPACE_SMUL]
  THEN REWRITE_TAC[COMPLEX_MUL_ASSOC;COMPLEX_MUL_CNJ;COMPLEX_POW_2;
  GSYM CX_MUL;GSYM REAL_POW_2] THEN
  IMP_REWRITE_TAC[REAL_CX; INPROD_SELF_REAL;
  REAL_OF_COMPLEX_MUL;REAL_OF_COMPLEX_CX;
  SQRT_MUL;INPROD_SELF_POS;REAL_LE_POW_2;POW_2_SQRT;NORM_POS_LE]);;

let CFUN_DIST_NZ = inner_space_prove(
  `!x y. x IN s /\ y IN s ==>
    (~(x=y) <=>  &0 < cfun_dist inprod x y):`,
        ONCE_REWRITE_TAC[GSYM CFUN_SUB_0] THEN
        REWRITE_TAC[cfun_dist;GSYM cfun_norm] THEN
    MESON_TAC[CFUN_NORM_NZ;INNER_SPACE_SUB]
        );;
(* ------------------------------------------------------------------------- *)
(* FINITE/INFINITE summation of cfun                                         *)
(* ------------------------------------------------------------------------- *)


let cfun_sum = new_definition`cfun_sum = iterate cfun_add`;;

let NEUTRAL_CFUN_ADD = prove
(`neutral cfun_add = cfun_zero`,REWRITE_TAC[neutral]
THEN MATCH_MP_TAC SELECT_UNIQUE
THEN MESON_TAC[CFUN_ADD_LID;CFUN_ADD_RID]);;

let MONOIDAL_CFUN_ADD = prove
 (`monoidal cfun_add`,
  REWRITE_TAC[monoidal; NEUTRAL_CFUN_ADD] THEN CFUN_ARITH_TAC);;

let CFUN_SUM_CLAUSES = prove
 (`(!f. cfun_sum {} f = cfun_zero) /\
 (!x f s. FINITE s ==>
         cfun_sum (x INSERT s) f =
         (if x IN s then cfun_sum s f else f x + cfun_sum s f))`,
 REWRITE_TAC[cfun_sum; GSYM NEUTRAL_CFUN_ADD] THEN
 ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
 MESON_TAC[ITERATE_CLAUSES;MONOIDAL_CFUN_ADD]);;

let CFUN_SUM_CLAUSES_NUMSEG =
  REWRITE_RULE[GSYM NEUTRAL_CFUN_ADD;  GSYM cfun_sum]
  (MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_CFUN_ADD);;
 let CFUN_SUM_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> cfun_sum (m..n) f = f(m) + cfun_sum(m+1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; CFUN_SUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let CFUN_SUM_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (cfun_sum (IMAGE f s) g = cfun_sum s (g o f))`,
  REWRITE_TAC[cfun_sum; GSYM NEUTRAL_CFUN_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_CFUN_ADD]);;

let NUMSEG_EMPTY_IMP = prove(`!m n. n < m ==> (m..n = {}) `,
   SIMP_TAC[NUMSEG_EMPTY] );;

let CFUN_SUM_TRIV_NUMSEG = prove
 (`!m n f. n < m ==> cfun_sum (m..n) f = cfun_zero`,
   SIMP_TAC[NUMSEG_EMPTY_IMP;CFUN_SUM_CLAUSES]);;

let CFUN_SUM_OFFSET = prove
 (`!p f m n. cfun_sum(m+p..n+p) f = cfun_sum(m..n) (\i. f(i + p))`,
  SIMP_TAC[NUMSEG_OFFSET_IMAGE; CFUN_SUM_IMAGE;
           EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF]);;

let CFUN_SUM_OFFSET_0 = prove
 (`!f m n. m <= n ==> (cfun_sum(m..n) f = cfun_sum(0..n-m) (\i. f(i + m)))`,
  SIMP_TAC[GSYM CFUN_SUM_OFFSET; ADD_CLAUSES; SUB_ADD]);;

let CFUN_SUM_CONST = prove
 (`!c s. FINITE s ==> (cfun_sum s (\n. c) = Cx(&(CARD s)) % c)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CFUN_SUM_CLAUSES; CARD_CLAUSES; GSYM REAL_OF_NUM_SUC] THEN
  REPEAT STRIP_TAC THEN CFUN_ARITH_TAC);;

let CFUN_SUM_EQ_0 = prove
 (`!f s. (!x:A. x IN s ==> (f(x) = cfun_zero)) ==> (cfun_sum s f = cfun_zero)`,
  REWRITE_TAC[cfun_sum; GSYM NEUTRAL_CFUN_ADD] THEN
  SIMP_TAC[ITERATE_EQ_NEUTRAL; MONOIDAL_CFUN_ADD]);;

let CFUN_SUM_0 = prove
 (`!s:A->bool. cfun_sum s (\n. cfun_zero) = cfun_zero`,
  SIMP_TAC[CFUN_SUM_EQ_0]);;



let CFUN_SUM_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (cfun_sum s f = cfun_sum s g)`,
  REWRITE_TAC[cfun_sum] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_CFUN_ADD]);;


let CFUN_SUM_SING = prove
 (`!f x. cfun_sum {x} f = f(x)`,
  SIMP_TAC[CFUN_SUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; CFUN_ADD_RID]);;

let CFUN_SUM_SING_NUMSEG = prove
 (`!f n. cfun_sum(n..n) f = f(n)`,
  SIMP_TAC[CFUN_SUM_SING; NUMSEG_SING]);;

let CFUN_SUM_EQ_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (cfun_sum(m..n) f = cfun_sum(m..n) g)`,
  MESON_TAC[CFUN_SUM_EQ; FINITE_NUMSEG; IN_NUMSEG]);;

let CFUN_SUM_IN_SPC = prove
 (`!g spc. is_cfun_subspace spc /\ (!n. g n IN spc) ==> !s. FINITE s
    ==> cfun_sum s g IN spc`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[CFUN_SUM_CLAUSES]
    THEN ASM_SIMP_TAC[CFUN_SUBSPACE_ZERO;CFUN_SUBSPACE_ADD]);;

let SLINEAR_CFUN_SUM = prove
 (`! spc f g.  is_cfun_subspace spc /\  (!n. g n IN spc)
     /\ is_set_linear_cop spc f
   ==> !s. FINITE s  ==> (f(cfun_sum s g) = cfun_sum s (f o g))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[CFUN_SUM_CLAUSES]
  THEN REPEAT STRIP_TAC
  THENL[ASM_MESON_TAC[SLINCOP_CFUN_ZERO];IMP_REWRITE_TAC[SLINCOP_ADD]]
  THEN Pa.EXISTS_TAC `spc:` THEN ASM_SIMP_TAC[CFUN_SUM_IN_SPC;o_DEF]);;

let SLINEAR_CFUN_SUM_IMP = prove
 (`! spc f g s.  is_cfun_subspace spc /\  (!n. g n IN spc)
   /\ is_set_linear_cop spc f
        /\FINITE s  ==> (f(cfun_sum s g) = cfun_sum s (f o g))`,
 MESON_TAC [SLINEAR_CFUN_SUM]);;

let LINEAR_CFUN_SUM = prove
 (`!f g s. is_linear_cop f /\ FINITE s ==>
        (f(cfun_sum s g) = cfun_sum s (f o g))`,
  GEN_TAC THEN GEN_TAC THEN SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CFUN_SUM_CLAUSES] THEN FIRST_ASSUM(fun th ->
    SIMP_TAC[MATCH_MP LINCOP_CFUN_ZERO th; MATCH_MP LINCOP_ADD th; o_THM]));;

let CFUN_SUM_ADD = prove
 (`!f g s. FINITE s ==>
        (cfun_sum s (\x. f(x) + g(x)) = cfun_sum s f + cfun_sum s g)`,
  SIMP_TAC[cfun_sum; ITERATE_OP; MONOIDAL_CFUN_ADD]);;


let CFUN_SUM_SMUL = prove
 (`!f a s. FINITE s ==> (cfun_sum s (\x. a % f(x) ) = a % cfun_sum s f)`,
   ONCE_REWRITE_TAC[MESON[] `a % (y:cfun) = (\x. a%x) y`] THEN
   SIMP_TAC[REWRITE_RULE [o_DEF]  (GSYM LINEAR_CFUN_SUM); SCALAR_LINCOP]);;

let CFUN_SUM_SUB = prove
 (`!f g s. FINITE s ==>
        (cfun_sum s (\x. f(x) - g(x)) = cfun_sum s f - cfun_sum s g)`,
  ONCE_REWRITE_TAC[CFUN_SUB_NEG] THEN
  ONCE_REWRITE_TAC[GSYM CFUN_SMUL_LID_NEG] THEN
  SIMP_TAC[CFUN_SUM_SMUL; CFUN_SUM_ADD]);;

let CUN_SUM_ADD_NUMSEG = prove
 (`!f g m n. cfun_sum(m..n) (\i. f(i) + g(i)) =
        cfun_sum(m..n) f + cfun_sum(m..n) g`,
  SIMP_TAC[CFUN_SUM_ADD; FINITE_NUMSEG]);;

let cfun_lim = new_definition
  `cfun_lim (s,inprod) f l net <=>
   is_inner_space (s,inprod) /\ l IN s /\ (!x. (f x) IN s) /\
   (!e. &0 < e ==> eventually (\x. cfun_dist inprod (f x) l < e) net)`;;

let CFUN_LIM_INNER_SPACE = prove
 (`!innerspc f l net. cfun_lim innerspc f l net ==> is_inner_space innerspc`,
  SIMP_TAC[FORALL_INNER_SPACE_THM;cfun_lim]);;

let is_bounded = new_definition
 `is_bounded  (s,inprod) h <=> is_inner_space (s,inprod)
     ==> is_closed_by s h /\ ?B. &0 < B /\
         (!x. x IN s ==> sqrt(real_of_complex(inprod (h x) (h x))) <=
           B * sqrt(real_of_complex(inprod x x)))`;;

let is_bounded_linear = new_definition
  `is_bounded_linear1 (s,inprod) h <=> is_inner_space (s,inprod)
     ==> is_linear_cop h /\ is_closed_by s h /\ ?B. &0 < B /\
         (!x. x IN s ==> sqrt(real_of_complex(inprod (h x) (h x))) <=
           B * sqrt(real_of_complex(inprod x x)))`;;

let COP_MUL_BOUNDED = prove
(`!s inprod h f.is_bounded  (s,inprod) h /\ is_bounded (s,inprod) f
    ==> is_bounded  (s,inprod) (h ** f)`,
  let lem = MESON[REAL_LE_TRANS;REAL_LE_LMUL]
   `&0 <= e /\ a <= b * c /\ d <= e * a ==> d <= e * b * c` in
 REWRITE_TAC[is_bounded;GSYM cfun_norm] THEN REPEAT STRIP_TAC
 THENL[ASM_MESON_TAC[IS_CLOSED_BY_COP_MUL;INNER_SPACE_IS_SUBSPACE];
 Pa.SUBGOAL_THEN
  `?B. &0 < B /\ (!x. x IN s ==> cfun_norm inprod (h (f x)) <=
       B * (cfun_norm inprod (f x))):` ASSUME_TAC]
  THENL[ASM_MESON_TAC[IS_CLOSED_BY_THM];
  Pa.SUBGOAL_THEN  `?B. &0 < B /\ (!x. x IN s ==> cfun_norm inprod (f x) <=
  B * cfun_norm inprod x)):` ASSUME_TAC]
  THENL[ASM_SIMP_TAC[];
  POP_ASSUM (X_CHOOSE_TAC `B1:real`)] THEN
  FIRST_X_ASSUM ((X_CHOOSE_TAC `B2:real`)) THEN Pa.EXISTS_TAC `B2 * B1:`
  THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[GSYM REAL_MUL_ASSOC;lem]
  THEN Pa.EXISTS_TAC `cfun_norm inprod (f x):` THEN
  ASM_SIMP_TAC[ REAL_ARITH `&0 < a ==> &0 <= a`;COP_MUL]);;


let SCALAR_BOUNDED = prove
 (`!a is. is_bounded is (\x:cfun. a % x) /\ is_linear_cop (\x:cfun. a % x)`,
        SIMP_TAC[FORALL_INNER_SPACE_THM;is_bounded;SCALAR_LINCOP;is_closed_by]
        THEN REPEAT STRIP_TAC
        THENL[ASM_MESON_TAC[INNER_SPACE_SMUL]; Pa.ASM_CASES_TAC `a = Cx(&0):`
         THENL[  Pa.EXISTS_TAC `&1:` THEN
             ASM_REWRITE_TAC[REAL_LT_01;CFUN_SMUL_LZERO;REAL_MUL_LID] THEN
                 ASM_MESON_TAC[SQRT_POS_LE;REAL_OF_COMPLEX_CX;SQRT_0;INPROD_ZERO;
                 INPROD_SELF_POS];Pa.EXISTS_TAC `norm a:` THEN
                 IMP_REWRITE_TAC[COMPLEX_NORM_NZ;REAL_LE_REFL;GSYM cfun_norm;
                 CFUN_NORM_SMUL]]]);;

let COP_SMUL_BOUNDED = prove
 (`!s inprod h a.is_bounded  (s,inprod) h ==> is_bounded  (s,inprod) (a % h)`,
    SIMP_TAC[COP_ARITH `a%h = (\x.a%x) ** h`;COP_MUL_BOUNDED;SCALAR_BOUNDED]);;

let COP_POW_BOUNDED = prove
 (`!s inprod h a.is_bounded  (s,inprod) h ==>
                !n. is_bounded  (s,inprod) (h pow n)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
        ASM_SIMP_TAC[cop_pow;COP_MUL_BOUNDED;SCALAR_BOUNDED;
        COP_ARITH `I = \x:cfun. Cx(&1) % x `]);;

let CFUN_LIM = prove
 (`cfun_lim (s,inprod) f l net  <=>
    is_inner_space (s,inprod) /\ l IN s /\ (!x. (f x) IN s) /\
        (trivial_limit net \/
        !e. &0 < e ==> ?y. (?x. netord(net) x y) /\
                           !x. netord(net) x y ==> cfun_dist inprod (f x) l < e)`,
  REWRITE_TAC[cfun_lim; eventually] THEN MESON_TAC[]);;

let CFUN_LIM_SLINEAR = prove
 (`!net:(A)net h f l s inprod.
        cfun_lim (s,inprod) f l net /\ is_set_linear_cop s h /\
                  is_bounded (s,inprod) h
                ==> cfun_lim (s,inprod) (\x.h (f x)) (h l) net`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CFUN_LIM] THEN
  ASM_CASES_TAC `trivial_limit (net:(A)net)` THEN
  ASM_SIMP_TAC[is_bounded;is_closed_by] THEN
  STRIP_TAC THEN  FIRST_ASSUM(fun thm -> FIRST_ASSUM (ASSUME_TAC o MP thm)) THEN
  FIRST_ASSUM STRIP_ASSUME_TAC  THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o Pa.SPEC `e / B:`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV;cfun_dist;REAL_LT_RDIV_EQ] THEN
  IMP_REWRITE_TAC[GSYM SLINCOP_SUB;INNER_SPACE_IS_SUBSPACE] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_MUL_SYM;INNER_SPACE_SUB]);;

let CFUN_LIM_LINEAR = prove
 (`!net:(A)net h f l s inprod.
        cfun_lim (s,inprod) f l net /\ is_bounded (s,inprod) h
                 /\ is_linear_cop h
                ==> cfun_lim (s,inprod) (\x.h (f x)) (h l) net`,
        SIMP_TAC[LINCOP_SLINCOP;CFUN_LIM_SLINEAR]);;

let cfun_sums = new_definition
 `cfun_sums innerspc f l s <=>
    cfun_lim innerspc (\n. cfun_sum (s INTER (0..n)) f) l sequentially`;;

let cfun_infsum = new_definition
 `cfun_infsum innerspc s f = @l.  cfun_sums innerspc f l s`;;

let cfun_summable = new_definition
 `cfun_summable innerspc s f = ?l. cfun_sums innerspc f l s`;;



let CFUN_SUMS_INNER_SPACE = prove
 (`!innerspc f l s. cfun_sums innerspc f l s ==> is_inner_space innerspc`,
  SIMP_TAC[FORALL_INNER_SPACE_THM;cfun_sums;cfun_lim]);;



let CFUN_SUMS_SUMMABLE = prove
 (`!f l s innerspc. cfun_sums innerspc f l s
     ==> cfun_summable innerspc s f`,
  REWRITE_TAC[cfun_summable] THEN MESON_TAC[]);;


let CFUN_SUMS_INFSUM = prove
 (`!f s innerspc. cfun_sums innerspc f (cfun_infsum innerspc s f) s <=>
     cfun_summable innerspc s f`,
  REWRITE_TAC[cfun_infsum;cfun_summable] THEN MESON_TAC[]);;



let CFUN_SUM_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (cfun_sum s f = cfun_sum s g)`,
    REWRITE_TAC[cfun_sum] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_CFUN_ADD]);;

 let CFUN_SUM_RESTRICT = prove
 (`!f s. FINITE s
         ==> (cfun_sum s (\x. if x IN s then f(x) else cfun_zero) =
                                        cfun_sum s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CFUN_SUM_EQ THEN ASM_SIMP_TAC[]);;

let CFUN_SUM_SUPERSET = prove
 (`!f u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = cfun_zero))
        ==> (cfun_sum v f = cfun_sum u f)`,
  SIMP_TAC[cfun_sum; GSYM NEUTRAL_CFUN_ADD; ITERATE_SUPERSET; MONOIDAL_CFUN_ADD]);;

let CFUN_LIM_SEQUENTIALLY = prove
 (`!f l s inprod. cfun_lim (s,inprod) f l sequentially <=>
       is_inner_space (s,inprod) /\  l IN s /\
          (!x. f x IN s)
          /\ (!e. &0 < e ==> ?N. !n. N <= n ==> cfun_dist inprod (f n) l < e)`,
  REWRITE_TAC[cfun_lim; EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]);;

let CFUN_LIM_NEG = prove
 (`!net f l innerspc.  cfun_lim innerspc f l net
     ==> cfun_lim innerspc (\x. --(f x)) (--l) net`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CFUN_LIM;cfun_dist] THEN
  IMP_REWRITE_TAC[CFUN_ARITH `--(x:cfun) - --y = --(x - y)`;
  INPROD_NEG;CFUN_SUBSPACE_SUB;CFUN_SUBSPACE_NEG]
  THEN MESON_TAC[INNER_SPACE_IS_SUBSPACE]);;


let CFUN_LIM_ADD = prove
 (`!net f g l m innerspc.
    cfun_lim innerspc f l net /\ cfun_lim innerspc g m net
        ==> cfun_lim innerspc (\x. f(x) + g(x)) (l+m) net`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM] THEN REPEAT GEN_TAC
  THEN REWRITE_TAC[CFUN_LIM;CONJ_ACI] THEN
  Pa.ASM_CASES_TAC `trivial_limit net:` THEN
  IMP_REWRITE_TAC[INNER_SPACE_ADD] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2` o REWRITE_RULE[MESON[]
  `!A B C D E F.A /\ B /\ C /\ D /\ (!x. E x) /\ (!x. F x)  /\ G
   <=> !x.   A  /\ B /\ C /\D   /\ G /\E x /\ F x `]) THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM( fun thm1 -> POP_ASSUM (fun thm2 -> MP_TAC (CONJS[thm1;thm2]))) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[CONJ_ACI] NET_DILEMMA))
  THEN MATCH_MP_TAC MONO_EXISTS THEN
  REPEAT STRIP_TAC THENL[  MATCH_MP_TAC REAL_LET_TRANS THEN
  Pa.EXISTS_TAC `cfun_dist inprod (f x') l + cfun_dist inprod (g x') m:` THEN
  ASM_MESON_TAC[REAL_HALF;CFUN_DIST_TRIANGLE_ADD;REAL_LT_ADD2];ASM_MESON_TAC[]]);;

let CFUN_LIM_SUB = prove
 (`!net f g l m innerspc.
    cfun_lim innerspc f l net /\ cfun_lim innerspc g m net
        ==> cfun_lim innerspc (\x. f(x) - g(x)) (l-m) net`,
  REWRITE_TAC[CFUN_SUB_NEG] THEN ASM_SIMP_TAC[CFUN_LIM_ADD;CFUN_LIM_NEG]);;

let CFUN_LIM_CONST = prove
 (`!net s inprod y. y IN s /\ is_inner_space (s,inprod)
     ==> cfun_lim (s,inprod) (\x. y) y net`,
  IMP_REWRITE_TAC[CFUN_LIM; CFUN_DIST_REFL; trivial_limit] THEN MESON_TAC[]);;

let CFUN_LIM_SMUL = prove
 (`!a net f l  innerspc.
    cfun_lim innerspc f l net
        ==> cfun_lim innerspc (\x. a% f(x)) (a%l) net`,
          REWRITE_TAC[FORALL_INNER_SPACE_THM] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC CFUN_LIM_LINEAR THEN
          ASM_SIMP_TAC[REWRITE_RULE [ETA_AX]SCALAR_BOUNDED]);;


let CFUN_LIM_NORM_UBOUND = prove
 (`!net:(A)net f l b s inprod.
      ~(trivial_limit net) /\
      cfun_lim (s,inprod) f l net /\
      eventually (\x. cfun_norm inprod (f x) <= b) net
      ==> cfun_norm inprod l <= b`,
  let STEP =  MESON[CFUN_NORM_SUB_INEQ;CFUN_NORM_SUB;
  REAL_ARITH `z <= b /\  x-z <= y ==> x  <= y+b`]
  `is_inner_space (s,inprod) /\ l IN s /\ f IN s
    ==> cfun_norm inprod l <= cfun_norm inprod (f-l) + b \/
         ~(cfun_norm inprod f <= b)` in
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[CFUN_LIM] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
  THEN ASM_REWRITE_TAC[eventually] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  Pa.SUBGOAL_THEN
   `?x:A. cfun_dist inprod (f x) l <
          cfun_norm inprod l - b /\ cfun_norm inprod(f x) <= b:`
  (CHOOSE_THEN MP_TAC) THENL [ASM_MESON_TAC[NET]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LT; REAL_LE_SUB_RADD; DE_MORGAN_THM;
  cfun_dist;GSYM cfun_norm] THEN MATCH_MP_TAC STEP THEN ASM_REWRITE_TAC[]
  );;


let CFUN_LIM_UNIQUE = prove
 (`!net:(A)net f l l' innerspc.
      ~(trivial_limit net) /\ cfun_lim innerspc f l net
      /\ cfun_lim innerspc f l' net ==> (l = l')`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN (fun thm -> ASSUME_TAC (REWRITE_RULE[cfun_lim] thm) THEN
  (ASSUME_TAC  (REWRITE_RULE[CFUN_SUB_REFL]  (MATCH_MP CFUN_LIM_SUB thm)))) THEN
  Pa.SUBGOAL_THEN `!e. &0 < e ==> cfun_norm inprod (l-l') <= e:` MP_TAC
  THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CFUN_LIM_NORM_UBOUND THEN
    MAP_EVERY Pa.EXISTS_TAC [`net:(A)net:`; `\x:A. cfun_zero:`;`s:`] THEN
    ASM_REWRITE_TAC[] THEN  IMP_REWRITE_TAC[CFUN_NORM_0; REAL_LT_IMP_LE] THEN
    ASM_MESON_TAC[eventually];
    DISCH_THEN(MP_TAC o Pa.SPEC `cfun_norm inprod (l-l') / &2:`) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    IMP_REWRITE_TAC[CFUN_DIST_NZ] THEN REWRITE_TAC[cfun_dist;GSYM cfun_norm] THEN
    DISCH_THEN (fun thm ->
     ASSUM_LIST(fun thms ->
       MP_TAC (REWRITE_RULE thms (Pa.SPECL [`inprod:`;`s:`] thm)))) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
         REAL_ARITH_TAC]);;

let CFUN_SERIES_ADD = prove
 (`!f g l l' s innerspc. cfun_sums innerspc f l s /\ cfun_sums innerspc g l' s
   ==> cfun_sums innerspc (\n.f n + g n) (l+l') s`,
  SIMP_TAC[cfun_sums; FINITE_INTER_NUMSEG; CFUN_SUM_ADD; CFUN_LIM_ADD]);;

let CFUN_SERIES_SUB = prove
 (`!f g l l' s innerspc. cfun_sums innerspc f l s /\ cfun_sums innerspc g l' s
   ==> cfun_sums innerspc (\n.f n - g n) (l-l') s`,
  SIMP_TAC[cfun_sums; FINITE_INTER_NUMSEG; CFUN_SUM_SUB; CFUN_LIM_SUB]);;

let CFUN_SERIES_SMUL = prove
 (`!a f l s innerspc. cfun_sums innerspc f l s
   ==> cfun_sums innerspc (\n.a% (f n))  (a%l) s`,
  SIMP_TAC[cfun_sums; FINITE_INTER_NUMSEG; CFUN_SUM_SMUL; CFUN_LIM_SMUL]);;

let CFUN_SERIES_UNIQUE = prove
 (`!f l l' s innerspc. cfun_sums innerspc f l s /\ cfun_sums innerspc f l' s
                        ==> (l = l')`,
  REWRITE_TAC[cfun_sums] THEN MESON_TAC[TRIVIAL_LIMIT_SEQUENTIALLY;
  CFUN_LIM_UNIQUE]);;

let CFUN_INFSUM_UNIQUE = prove
 (`!f l s innerspc. cfun_sums innerspc f l s ==> cfun_infsum innerspc s f = l`,
  MESON_TAC[CFUN_SERIES_UNIQUE; CFUN_SUMS_INFSUM; cfun_summable]);;

let INFSUM_IN_SPC = prove
(`!spc inprod f l s. cfun_summable (spc,inprod) s f ==>
    (cfun_infsum (spc,inprod) s f) IN spc`,
        REWRITE_TAC[cfun_summable;cfun_lim;cfun_infsum;cfun_sums]
        THEN MESON_TAC[CFUN_LIM_UNIQUE]);;

let CFUN_SERIES_0 = prove
 (`!s spc inprod. is_inner_space (spc,inprod) ==>
  cfun_sums (spc,inprod)  (\n. cfun_zero) (cfun_zero) s`,
  IMP_REWRITE_TAC[cfun_sums; CFUN_SUM_0; CFUN_LIM_CONST;INNER_SPACE_ZERO]);;

 let CFUN_SERIES_FINITE = prove
 (`!f s spc inprod. (!x. f x IN spc)  /\ is_inner_space (spc,inprod) /\
      FINITE s ==> cfun_sums (spc,inprod) f (cfun_sum s f) s`,
  REPEAT STRIP_TAC THEN POP_ASSUM (fun thm -> MP_TAC thm THEN ASSUME_TAC thm)
  THEN REWRITE_TAC[num_FINITE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[cfun_sums; CFUN_LIM_SEQUENTIALLY]
  THEN IMP_REWRITE_TAC[CFUN_SUM_IN_SPC;FINITE_INTER_NUMSEG;
  INNER_SPACE_IS_SUBSPACE] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `n:num` THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s INTER (0..m) = s`
   (fun th -> ASM_SIMP_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[LE_TRANS;CFUN_DIST_REFL]);;

let CFUN_SERIES_SLINEAR = prove
 (`!f h l s spc inprod. cfun_sums (spc,inprod) f l s /\
     is_set_linear_cop spc h  /\ is_bounded (spc,inprod) h /\
         (!n. f n IN spc)
       ==> cfun_sums (spc,inprod) (\n. h(f n)) (h l) s `,
           REWRITE_TAC[cfun_sums] THEN REPEAT STRIP_TAC THEN
           Pa.SUBGOAL_THEN
           `!n. cfun_sum (s INTER(0..n)) (\x. h(f x)) = h(cfun_sum (s INTER(0..n)) f):`
                 ASSUME_TAC
                 THENL[IMP_REWRITE_TAC[FINITE_INTER; FINITE_NUMSEG;
           GSYM(REWRITE_RULE[o_DEF] SLINEAR_CFUN_SUM_IMP)] THEN
                   ASM_MESON_TAC[INNER_SPACE_IS_SUBSPACE;CFUN_LIM_INNER_SPACE];
                   ASM_SIMP_TAC[cfun_sums;CFUN_LIM_SLINEAR]]);;

let CFUN_INFSUM_0 = prove
 (`!is s. is_inner_space (spc,inprod) ==>
    cfun_infsum (spc,inprod) s (\i. cfun_zero) = cfun_zero`,
 REPEAT STRIP_TAC THEN MATCH_MP_TAC CFUN_INFSUM_UNIQUE
 THEN ASM_SIMP_TAC[CFUN_SERIES_0]);;

let CFUN_SERIES_LINEAR = prove
 (`!f h l s innerspc. cfun_sums innerspc f l s /\ is_linear_cop h
   /\ is_bounded innerspc h
 ==> cfun_sums innerspc (\n. h(f n)) (h l) s `,
  SIMP_TAC[cfun_sums; FINITE_INTER; FINITE_NUMSEG;
           GSYM(REWRITE_RULE[o_DEF] LINEAR_CFUN_SUM);
                   FORALL_INNER_SPACE_THM;CFUN_LIM_LINEAR]);;

let CFUN_INFSUM_SLINEAR = prove
 (`!f h l s spc inprod. cfun_summable (spc,inprod) s f /\
   is_set_linear_cop spc h  /\ is_bounded (spc,inprod) h /\
     (!n. f n IN spc)
           ==> cfun_infsum (spc,inprod) s (\n. h(f n)) =
                       h (cfun_infsum (spc,inprod) s f)`,
        REPEAT STRIP_TAC THEN MATCH_MP_TAC CFUN_INFSUM_UNIQUE THEN
  MATCH_MP_TAC CFUN_SERIES_SLINEAR THEN ASM_REWRITE_TAC[CFUN_SUMS_INFSUM]);;

let CFUN_INFSUM_LINEAR = prove
 (`!f h l s innerspc. cfun_summable innerspc s f /\ is_linear_cop h
   /\ is_bounded innerspc h
           ==> cfun_infsum innerspc s (\n. h(f n)) = h(cfun_infsum innerspc s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CFUN_INFSUM_UNIQUE THEN
  MATCH_MP_TAC CFUN_SERIES_LINEAR THEN ASM_REWRITE_TAC[CFUN_SUMS_INFSUM]);;

 let CFUN_INFSUM_SMUL = prove
 (`!a f innerspc. cfun_summable innerspc s f
   ==>  cfun_infsum innerspc s (\n.a% (f n)) = a % (cfun_infsum innerspc s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CFUN_INFSUM_UNIQUE THEN
  MATCH_MP_TAC CFUN_SERIES_SMUL THEN ASM_REWRITE_TAC[CFUN_SUMS_INFSUM]);;

  let CFUN_SERIES_RESTRICT = prove
 (`!f k l innerspc.
        cfun_sums innerspc (\n. if n IN k then f(n) else cfun_zero)  l (:num)
                        <=> cfun_sums innerspc f  l k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cfun_sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  REWRITE_TAC[INTER_UNIV] THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[] `
  cfun_sum s f = cfun_sum t f /\ cfun_sum t f = cfun_sum t g
                        ==> cfun_sum s f = cfun_sum t g`)
        THEN CONJ_TAC THENL
   [MATCH_MP_TAC CFUN_SUM_SUPERSET THEN SET_TAC[];
    MATCH_MP_TAC CFUN_SUM_EQ THEN SIMP_TAC[IN_INTER]]);;

let CFUN_SUMS_FINITE_DIFF = prove
 (`!f l s t spc inpord.
        t SUBSET s /\ FINITE t /\ (!x. f x IN spc) /\
                cfun_sums (spc,inpord) f l s
        ==> cfun_sums (spc,inpord) f (l - cfun_sum t f)  (s DIFF t)`,
  let lem = MESON[]`(P /\ Q /\ E ==> C)<=> (E ==> P ==> Q ==>C)` in
   REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP CFUN_SUMS_INNER_SPACE)
   THEN ASSUME_TAC (REWRITE_RULE[lem] CFUN_SERIES_FINITE)
  THEN  REPEAT (FIRST_X_ASSUM (fun thm1 ->
     POP_ASSUM (fun thm2 -> ASSUME_TAC ( MATCH_MP thm2 thm1))))
  THEN POP_ASSUM MP_TAC THEN  POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM CFUN_SERIES_RESTRICT] THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CFUN_SERIES_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_DIFF] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o GEN_REWRITE_RULE I [SUBSET]) THEN
  MAP_EVERY ASM_CASES_TAC [`(x:num) IN s`; `(x:num) IN t`] THEN
  ASM_REWRITE_TAC[CFUN_SUB_REFL;CFUN_SUB_RID]);;

let CFUN_SUMS_OFFSET = prove
 (`!f l m n s inprod.
      cfun_sums (s,inprod) f l (from m) /\ (!x. f x IN s) /\ m < n
        ==> cfun_sums (s,inprod) f (l - cfun_sum (m..(n-1)) f) (from n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `from n = from m DIFF (m..(n-1))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_FROM; IN_DIFF; IN_NUMSEG] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC CFUN_SUMS_FINITE_DIFF THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    SIMP_TAC[SUBSET; IN_FROM; IN_NUMSEG]]);;

let CFUN_SUMMABLE_OFFSET = prove
 (`!f s inprod n. cfun_summable (s,inprod) (from m)  f  /\ (!x. f x IN s)
                /\ m < n ==> cfun_summable (s,inprod) (from n)  f`,
   MESON_TAC[cfun_summable;CFUN_SUMS_OFFSET]);;

let CFUN_INFSUM_OFFSET = prove
(`!f s inprod n m. cfun_summable (s,inprod) (from m) f
   /\ (!x. f x IN s) /\ m < n ==>
 cfun_infsum (s,inprod) (from m)  f =
   cfun_sum (m..n-1) f + cfun_infsum (s,inprod) (from n) f`,
 REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CFUN_SUMS_INFSUM] THEN
 DISCH_THEN(MP_TAC o MATCH_MP CFUN_SUMS_OFFSET) THEN
 MESON_TAC[CFUN_ARITH `x:cfun = y + z <=> z = x - y`;CFUN_INFSUM_UNIQUE]);;

let CFUN_SUMS_REINDEX = prove
 (`!f innerspc n l k. cfun_sums innerspc (\x. f(x+k)) l (from n) <=>
     cfun_sums innerspc f l (from (n+k))`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[cfun_sums; FROM_INTER_NUMSEG] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CFUN_SUM_OFFSET] THEN
  REWRITE_TAC[CFUN_LIM_SEQUENTIALLY] THEN EQ_TAC THEN SIMP_TAC[]
  THEN REPEAT STRIP_TAC THENL[Pa.ASM_CASES_TAC ` k <= x:` THENL[
  FIRST_ASSUM(fun th -> ASM_MESON_TAC[SUB_ADD; Pa.SPEC `x-k:` th]);
  IMP_REWRITE_TAC[CFUN_SUM_TRIV_NUMSEG;INNER_SPACE_ZERO] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC];ALL_TAC;ALL_TAC]
  THEN
  ASM_MESON_TAC[ARITH_RULE `N + k:num <= n ==> n = (n - k) + k /\ N <= n - k`;
                ARITH_RULE `N + k:num <= n ==> N <= n + k`]);;

let CFUN_SUMMABLE_REINDEX = prove
(`!f innerspc n  k. cfun_summable innerspc (from n) (\x. f(x+k))  <=>
     cfun_summable innerspc (from (n+k)) f`,
         MESON_TAC[cfun_summable;CFUN_SUMS_REINDEX]);;

let CFUN_INFSUM_REINDEX = prove
   (`!f innerspc n k.  cfun_summable  innerspc (from n) (\x. f (x + k)) ==>
       cfun_infsum innerspc (from (n+k)) f =
                        cfun_infsum innerspc (from n) (\x. f(x+k)) `,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CFUN_INFSUM_UNIQUE
   THEN ASM_SIMP_TAC[GSYM CFUN_SUMS_REINDEX;CFUN_SUMS_INFSUM]);;

(* ------------------------------------------------------------------------- *)
(* FINITE/INFINITE summation of cop                                         *)
(* ------------------------------------------------------------------------- *)
let cop_sum = new_definition`cop_sum s f = \x. cfun_sum s (\n.(f n) x)`;;

let COP_BINOMIAL_THEOREM = prove
 (`!n op1 op2.
        op1 ** op2 = op2 ** op1 /\ is_linear_cop op1 /\ is_linear_cop op2
        ==> (op1 + op2) pow n =
            cop_sum (0..n)
            (\k. Cx (&(binom (n,k))) % (op1 pow k ** op2 pow (n - k)))`,
          INDUCT_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cop_pow;cop_sum] THEN
          REWRITE_TAC[CFUN_SUM_SING_NUMSEG; binom; SUB_REFL; cop_pow; COP_MUL_LID;
          I_THM;GSYM I_DEF;COP_SMUL_LID] THEN
          SIMP_TAC[CFUN_SUM_CLAUSES_LEFT; ADD1; ARITH_RULE `0 <= n + 1`;
          CFUN_SUM_OFFSET] THEN
          ASM_SIMP_TAC[cop_pow; binom; GSYM ADD1;COP_MUL_LID;COP_SMUL_LID;cop_sum]
          THEN ASM_SIMP_TAC[LINEAR_CFUN_SUM;ADD_LINCOP;COP_MUL;FINITE_NUMSEG;
          o_DEF;COP_ADD_MUL_RDISTRIB] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD;CX_ADD;COP_ADD_RDISTRIB;
          CUN_SUM_ADD_NUMSEG;SUB_0;GSYM COP_ADD;  COP_ADD_THM] THEN
          MATCH_MP_TAC( MESON[COP_ADD_AC] `a = e /\ b = c + d ==> a + b = c + d + e`)
          THEN CONJ_TAC THEN REWRITE_TAC[GSYM COP_MUL;GSYM COP_MUL_THM; GSYM I_DEF
          ; COP_MUL_RID]
          THENL [ASM_SIMP_TAC[GSYM LINCOP_MUL_RMUL;SUB_SUC;COP_MUL];
          SIMP_TAC[GSYM cop_pow;GSYM COP_MUL_ASSOC]] THEN
          SIMP_TAC[ADD1; SYM(REWRITE_CONV[CFUN_SUM_OFFSET]
          `cfun_sum(m+1..n+1) (\i. f i)`)] THEN
          REWRITE_TAC[CFUN_SUM_CLAUSES_NUMSEG; GSYM ADD1; LE_SUC; LE_0] THEN
          SIMP_TAC[CFUN_SUM_CLAUSES_LEFT; LE_0; BINOM_LT; LT; COP_SMUL_LID;
          SUB_0; cop_pow;binom; COP_SMUL_LZERO;COP_ZERO;CFUN_ADD_RID;COP_MUL_LID]
          THEN ASM_SIMP_TAC[GSYM COP_ADD; COP_MUL_RID;COP_EQ_ADD_LCANCEL;
          LINCOP_MUL_RMUL;ARITH;ETA_AX;GSYM COP_MUL_ASSOC] THEN
          ABS_TAC THEN RULE_ASSUM_TAC GSYM THEN MATCH_MP_TAC CFUN_SUM_EQ_NUMSEG THEN
          SIMP_TAC[ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; cop_pow]
          THEN ASM_SIMP_TAC[COP_POW_COMMUTE_N] THEN
          SIMP_TAC[COP_POW_COMMUTE_N; COP_MUL_ASSOC]);;

let cop_sums = new_definition
 `cop_sums (s,inprod) f l set <=> !x. x IN s ==>
                cfun_sums (s,inprod) (\n.(f n) x) (l x) set`;;

let cop_infsum = new_definition
 `cop_infsum innerspc s f = @l. cop_sums innerspc f l s`;;


let cop_summable = new_definition
 `cop_summable innerspc s f = ?l. cop_sums innerspc f l s`;;

let COP_SUMS_INFSUM = prove
 (`!f s innerspc. cop_sums innerspc f (cop_infsum innerspc s f) s <=>
     cop_summable innerspc s f`,
  REWRITE_TAC[cop_infsum;cop_summable] THEN MESON_TAC[]);;


let COP_SERIES_UNIQUE = prove
 (`!sp inprod f s l l' x. x IN sp /\
  cop_sums (sp,inprod) f l s /\ cop_sums (sp,inprod) f l' s ==>  l x = l' x`,
  MESON_TAC[cop_sums;CFUN_SERIES_UNIQUE]);;



let COP_INFSUM_UNIQUE = prove
 (`!sp inprod f s l l' x. x IN sp /\
  cop_sums (sp,inprod) f l s ==> cop_infsum (sp,inprod) s f x = l x`,
  MESON_TAC[cop_summable;COP_SERIES_UNIQUE;COP_SUMS_INFSUM]);;


let exp_sums =   new_definition
 `exp_sums innerspc  (op:cfun->cfun) l  <=>
  cop_sums innerspc (\n. Cx (inv(&(FACT n))) % (op pow n )) l (from 0)`;;

let exp_summable =   new_definition
 `exp_summable innerspc  (op:cfun->cfun) <=>
   cop_summable innerspc (from 0) (\n. Cx (inv(&(FACT n))) % (op pow n ))`;;


 let EXP_SUMS_CLOSED_BY =  prove
 (`!s inprod op l.  exp_sums (s,inprod) op l ==> (!x. x IN s ==> (l x) IN s)`,
   SIMP_TAC[exp_sums;cop_sums;cfun_sums;cfun_lim]);;

let LINCOP_EXP = prove
 (`!s inprod op l. is_linear_cop op /\ exp_sums (s,inprod) op l
    ==> is_set_linear_cop s l`,
        let lem = [ASM_MESON_TAC[CFUN_SUMS_INNER_SPACE;INNER_SPACE_ADD;
        INNER_SPACE_SMUL];
        ASM_SIMP_TAC[LINCOP_ADD;POW_LINCOP;SMUL_LINCOP;CFUN_SERIES_ADD;
        LINCOP_SMUL;CFUN_SERIES_SMUL]] in
        REWRITE_TAC[exp_sums;cop_sums;is_set_linear_cop] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC CFUN_SERIES_UNIQUE
        THENL[Pa.EXISTS_TAC `(\n. (Cx (inv (&(FACT n))) % (op pow n)) (x+y)):`;
        Pa.EXISTS_TAC `(\n. (Cx (inv (&(FACT n))) % (op pow n)) (a%x)):`] THEN
        MAP_EVERY Pa.EXISTS_TAC [`(from 0):`;`(s,inprod):`] THEN STRIP_TAC
        THENL lem@lem);;

let LINCOP_EXP_MUL = prove
 (`!s inprod op1 l1 op2 l2. is_linear_cop op1 /\ exp_sums (s,inprod) op1 l1
    /\  is_linear_cop op2 /\ exp_sums (s,inprod) op2 l2
    ==> is_set_linear_cop s (l1 ** l2)`,
     REWRITE_TAC[is_set_linear_cop;COP_MUL_THM] THEN REPEAT STRIP_TAC THEN
        IMP_REWRITE_TAC[SLINCOP_ADD;SLINCOP_SMUL] THEN
        ASM_MESON_TAC[LINCOP_EXP;EXP_SUMS_CLOSED_BY]);;

let COP_ZERO_SUM = prove
 (`!x n. cfun_sum (0..n) (\n. (Cx (inv(&(FACT n))) % (cop_zero pow n ))  x) = x`,
         SIMP_TAC[CFUN_SUM_CLAUSES_LEFT;LE_0;ADD_CLAUSES;cop_pow;FACT] THEN
         REPEAT STRIP_TAC THEN Pa.ASM_CASES_TAC `n=0:`
         THENL[ASM_SIMP_TAC[NUMSEG_EMPTY_IMP; NUM_LT_CONV `0 < 1`;CFUN_SUM_CLAUSES];
         ASM_SIMP_TAC[CFUN_SUM_OFFSET_0;ARITH_RULE `~(n=0) ==> 1 <= n`;COP_POW_ZERO;
         COP_SMUL_RZERO;COP_ZERO_THM;CFUN_SUM_CONST;FINITE_NUMSEG;CARD_NUMSEG]]
         THEN COP_ARITH_TAC);;

let COP_EXP_0 = prove
 (`!is. is_inner_space is ==> exp_sums is cop_zero I`,
         SIMP_TAC[FORALL_INNER_SPACE_THM;exp_sums;cop_sums;cfun_sums;
         COP_ZERO_SUM;FROM_INTER_NUMSEG;I_DEF;CFUN_LIM_CONST]);;

let CFUN_VSUM_SCALAR = prove
 (`!f q s.  FINITE s ==> cfun_sum s (\n.(f n) % x) = (vsum s f) % x`,
   GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
   SIMP_TAC[CFUN_SUM_CLAUSES;VSUM_CLAUSES;COMPLEX_VEC_0;
   CFUN_SMUL_LZERO;CFUN_ADD_RDISTRIB]);;

let COP_EXP_SCALAR = prove
 (`!is a .
      is_inner_space is==> exp_sums is (\x.a%x) (\x.(cexp a)%x)`,
         MP_TAC CEXP_CONVERGES THEN
         SIMP_TAC[FORALL_INNER_SPACE_THM;exp_sums;cop_sums;cfun_sums;CFUN_LIM;LIM;sums;
         CFUN_VSUM_SCALAR;FINITE_INTER;FINITE_NUMSEG;COP_POW_SCALAR;COP_SMUL;
         CFUN_SMUL_ASSOC;TRIVIAL_LIMIT_SEQUENTIALLY;CX_INV;
         COMPLEX_FIELD `inv a * b  = b / a`; cfun_dist;GSYM CFUN_SUB_RDISTRIB] THEN
         IMP_REWRITE_TAC[INNER_SPACE_SMUL;INPROD_RSMUL;INPROD_LSMUL] THEN
         REWRITE_TAC[COMPLEX_MUL_CNJ;COMPLEX_MUL_ASSOC;COMPLEX_POW_2;
         GSYM CX_MUL;GSYM REAL_POW_2;SQRT_MUL] THEN
         IMP_REWRITE_TAC[REAL_OF_COMPLEX_MUL;REAL_CX;INPROD_SELF_REAL;
         REAL_OF_COMPLEX_CX;NORM_POS_LE;POW_2_SQRT;SQRT_MUL;GSYM dist;
         GSYM cfun_norm;INPROD_SELF_POS;REAL_LE_POW_2;DIST_POS_LE] THEN
         REPEAT STRIP_TAC THEN Pa.ASM_CASES_TAC `x = cfun_zero:`
        THENL[ASM_MESON_TAC[CFUN_NORM_0;REAL_MUL_RZERO];
         REPEAT (IMP_REWRITE_TAC[GSYM REAL_LT_RDIV_EQ;
         GSYM CFUN_NORM_NZ;REAL_LT_DIV])]);;



let cop_exp =   new_definition
 `cop_exp is (op:cfun->cfun)  =
   cop_infsum is (from 0) (\n. Cx (inv(&(FACT n))) % (op pow n ))`;;

let EXP_SUMS_INFSUM = prove
 (`!f s innerspc. exp_sums innerspc op (cop_exp innerspc op)  <=>
     exp_summable innerspc op`,
  SIMP_TAC[exp_sums;cop_exp;exp_summable;COP_SUMS_INFSUM] );;

let COP_EXP_CLOSED_BY =  prove
 (`!s inprod op l.  exp_summable (s,inprod) op  ==>
                (!x. x IN s ==> (cop_exp (s,inprod) op ) x IN s)`,
   MESON_TAC[EXP_SUMS_INFSUM;EXP_SUMS_CLOSED_BY]);;

let COP_EXP_ZERO = prove
(`!s inprod x. x IN s /\ is_inner_space(s,inprod) ==>
        cop_exp (s,inprod) cop_zero x = I x`,
 MESON_TAC[I_THM;cop_exp;COP_INFSUM_UNIQUE;GSYM exp_sums;COP_EXP_0;GSYM I_DEF]);;

let COP_EXP_CEXP = prove
 (`!s inprod a x.   x IN s /\ is_inner_space (s,inprod)
    ==> cop_exp (s,inprod) (\y.a%y) x = cexp a % x`,
MESON_TAC[cop_exp;COP_INFSUM_UNIQUE;GSYM exp_sums;COP_EXP_SCALAR]);;


let EXP_LINCOP = prove
 (`!s inprod op. exp_summable (s,inprod) op /\ is_linear_cop op
            ==> is_set_linear_cop s (cop_exp (s,inprod) op)`,
  MESON_TAC[EXP_SUMS_INFSUM;LINCOP_EXP]);;

let EXP_MUL_LINCOP = prove
  (`!s inprod op1 op2. exp_summable (s,inprod) op1 /\ is_linear_cop op1
     /\ exp_summable (s,inprod) op2 /\ is_linear_cop op2
         ==>
         is_set_linear_cop s ((cop_exp (s,inprod) op1) ** (cop_exp (s,inprod) op2))`,
        MESON_TAC[EXP_SUMS_INFSUM;LINCOP_EXP_MUL]);;
