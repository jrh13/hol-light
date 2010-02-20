(* ========================================================================= *)
(* Theory of lists, plus characters and strings as lists of characters.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

let LIST_INDUCT_TAC =
  let list_INDUCT = prove
   (`!P:(A)list->bool. P [] /\ (!h t. P t ==> P (CONS h t)) ==> !l. P l`,
    MATCH_ACCEPT_TAC list_INDUCT) in
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN GEN_TAC THEN DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* Basic definitions.                                                        *)
(* ------------------------------------------------------------------------- *)

let HD = new_recursive_definition list_RECURSION
  `HD(CONS (h:A) t) = h`;;

let TL = new_recursive_definition list_RECURSION
  `TL(CONS (h:A) t) = t`;;

let APPEND = new_recursive_definition list_RECURSION
  `(!l:(A)list. APPEND [] l = l) /\
   (!h t l. APPEND (CONS h t) l = CONS h (APPEND t l))`;;

let REVERSE = new_recursive_definition list_RECURSION
  `(REVERSE [] = []) /\
   (REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x])`;;

let LENGTH = new_recursive_definition list_RECURSION
  `(LENGTH [] = 0) /\
   (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t))`;;

let MAP = new_recursive_definition list_RECURSION
  `(!f:A->B. MAP f NIL = NIL) /\
   (!f h t. MAP f (CONS h t) = CONS (f h) (MAP f t))`;;

let LAST = new_recursive_definition list_RECURSION
  `LAST (CONS (h:A) t) = if t = [] then h else LAST t`;;

let REPLICATE = new_recursive_definition num_RECURSION
  `(REPLICATE 0 x = []) /\
   (REPLICATE (SUC n) x = CONS x (REPLICATE n x))`;;

let NULL = new_recursive_definition list_RECURSION
  `(NULL [] = T) /\
   (NULL (CONS h t) = F)`;;

let ALL = new_recursive_definition list_RECURSION
  `(ALL P [] = T) /\
   (ALL P (CONS h t) <=> P h /\ ALL P t)`;;

let EX = new_recursive_definition list_RECURSION
  `(EX P [] = F) /\
   (EX P (CONS h t) <=> P h \/ EX P t)`;;

let ITLIST = new_recursive_definition list_RECURSION
  `(ITLIST f [] b = b) /\
   (ITLIST f (CONS h t) b = f h (ITLIST f t b))`;;

let MEM = new_recursive_definition list_RECURSION
  `(MEM x [] <=> F) /\
   (MEM x (CONS h t) <=> (x = h) \/ MEM x t)`;;

let ALL2_DEF = new_recursive_definition list_RECURSION
  `(ALL2 P [] l2 <=> (l2 = [])) /\
   (ALL2 P (CONS h1 t1) l2 <=>
        if l2 = [] then F
        else P h1 (HD l2) /\ ALL2 P t1 (TL l2))`;;

let ALL2 = prove
 (`(ALL2 P [] [] <=> T) /\
   (ALL2 P (CONS h1 t1) [] <=> F) /\
   (ALL2 P [] (CONS h2 t2) <=> F) /\
   (ALL2 P (CONS h1 t1) (CONS h2 t2) <=> P h1 h2 /\ ALL2 P t1 t2)`,
  REWRITE_TAC[distinctness "list"; ALL2_DEF; HD; TL]);;

let MAP2_DEF = new_recursive_definition list_RECURSION
  `(MAP2 f [] l = []) /\
   (MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l)))`;;

let MAP2 = prove
 (`(MAP2 f [] [] = []) /\
   (MAP2 f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (MAP2 f t1 t2))`,
  REWRITE_TAC[MAP2_DEF; HD; TL]);;

let EL = new_recursive_definition num_RECURSION
  `(EL 0 l = HD l) /\
   (EL (SUC n) l = EL n (TL l))`;;

let FILTER = new_recursive_definition list_RECURSION
  `(FILTER P [] = []) /\
   (FILTER P (CONS h t) = if P h then CONS h (FILTER P t) else FILTER P t)`;;

let ASSOC = new_recursive_definition list_RECURSION
  `ASSOC a (CONS h t) = if FST h = a then SND h else ASSOC a t`;;

let ITLIST2_DEF = new_recursive_definition list_RECURSION
  `(ITLIST2 f [] l2 b = b) /\
   (ITLIST2 f (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b))`;;

let ITLIST2 = prove
 (`(ITLIST2 f [] [] b = b) /\
   (ITLIST2 f (CONS h1 t1) (CONS h2 t2) b = f h1 h2 (ITLIST2 f t1 t2 b))`,
  REWRITE_TAC[ITLIST2_DEF; HD; TL]);;

let ZIP_DEF = new_recursive_definition list_RECURSION
  `(ZIP [] l2 = []) /\
   (ZIP (CONS h1 t1) l2 = CONS (h1,HD l2) (ZIP t1 (TL l2)))`;;

let ZIP = prove
 (`(ZIP [] [] = []) /\
   (ZIP (CONS h1 t1) (CONS h2 t2) = CONS (h1,h2) (ZIP t1 t2))`,
  REWRITE_TAC[ZIP_DEF; HD; TL]);;

(* ------------------------------------------------------------------------- *)
(* Various trivial theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

let NOT_CONS_NIL = prove
 (`!(h:A) t. ~(CONS h t = [])`,
  REWRITE_TAC[distinctness "list"]);;

let LAST_CLAUSES = prove
 (`(LAST [h:A] = h) /\
   (LAST (CONS h (CONS k t)) = LAST (CONS k t))`,
  REWRITE_TAC[LAST; NOT_CONS_NIL]);;

let APPEND_NIL = prove
 (`!l:A list. APPEND l [] = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let APPEND_ASSOC = prove
 (`!(l:A list) m n. APPEND l (APPEND m n) = APPEND (APPEND l m) n`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let REVERSE_APPEND = prove
 (`!(l:A list) m. REVERSE (APPEND l m) = APPEND (REVERSE m) (REVERSE l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; REVERSE; APPEND_NIL; APPEND_ASSOC]);;

let REVERSE_REVERSE = prove
 (`!l:A list. REVERSE(REVERSE l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; REVERSE_APPEND; APPEND]);;

let CONS_11 = prove
 (`!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)`,
  REWRITE_TAC[injectivity "list"]);;

let list_CASES = prove
 (`!l:(A)list. (l = []) \/ ?h t. l = CONS h t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CONS_11; NOT_CONS_NIL] THEN
  MESON_TAC[]);;

let LENGTH_APPEND = prove
 (`!(l:A list) m. LENGTH(APPEND l m) = LENGTH l + LENGTH m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES]);;

let MAP_APPEND = prove
 (`!f:A->B. !l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]);;

let LENGTH_MAP = prove
 (`!l. !f:A->B. LENGTH (MAP f l) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH]);;

let LENGTH_EQ_NIL = prove
 (`!l:A list. (LENGTH l = 0) <=> (l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_CONS_NIL; NOT_SUC]);;

let LENGTH_EQ_CONS = prove
 (`!l n. (LENGTH l = SUC n) <=> ?h t. (l = CONS h t) /\ (LENGTH t = n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[SUC_INJ; CONS_11] THEN MESON_TAC[]);;

let MAP_o = prove
 (`!f:A->B. !g:B->C. !l. MAP (g o f) l = MAP g (MAP f l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; o_THM]);;

let MAP_EQ = prove
 (`!f g l. ALL (\x. f x = g x) l ==> (MAP f l = MAP g l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL] THEN ASM_MESON_TAC[]);;

let ALL_IMP = prove
 (`!P Q l. (!x. MEM x l /\ P x ==> Q x) /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; ALL] THEN ASM_MESON_TAC[]);;

let NOT_EX = prove
 (`!P l. ~(EX P l) <=> ALL (\x. ~(P x)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; ALL; DE_MORGAN_THM]);;

let NOT_ALL = prove
 (`!P l. ~(ALL P l) <=> EX (\x. ~(P x)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; ALL; DE_MORGAN_THM]);;

let ALL_MAP = prove
 (`!P f l. ALL P (MAP f l) <=> ALL (P o f) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; MAP; o_THM]);;

let ALL_T = prove
 (`!l. ALL (\x. T) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL]);;

let MAP_EQ_ALL2 = prove
 (`!l m. ALL2 (\x y. f x = f y) l m ==> (MAP f l = MAP f m)`,
  REPEAT LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2; CONS_11] THEN
  ASM_MESON_TAC[]);;

let ALL2_MAP = prove
 (`!P f l. ALL2 P (MAP f l) l <=> ALL (\a. P (f a) a) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP; ALL]);;

let MAP_EQ_DEGEN = prove
 (`!l f. ALL (\x. f(x) = x) l ==> (MAP f l = l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; CONS_11] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let ALL2_AND_RIGHT = prove
 (`!l m P Q. ALL2 (\x y. P x /\ Q x y) l m <=> ALL P l /\ ALL2 Q l m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; ALL2] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; ALL2] THEN
  REWRITE_TAC[CONJ_ACI]);;

let ITLIST_APPEND = prove
 (`!f a l1 l2. ITLIST f (APPEND l1 l2) a = ITLIST f l1 (ITLIST f l2 a)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; APPEND]);;

let ITLIST_EXTRA = prove
 (`!l. ITLIST f (APPEND l [a]) b = ITLIST f l (f a b)`,
  REWRITE_TAC[ITLIST_APPEND; ITLIST]);;

let ALL_MP = prove
 (`!P Q l. ALL (\x. P x ==> Q x) l /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

let AND_ALL = prove
 (`!l. ALL P l /\ ALL Q l <=> ALL (\x. P x /\ Q x) l`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; CONJ_ACI]);;

let EX_IMP = prove
 (`!P Q l. (!x. MEM x l /\ P x ==> Q x) /\ EX P l ==> EX Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; EX] THEN ASM_MESON_TAC[]);;

let ALL_MEM = prove
 (`!P l. (!x. MEM x l ==> P x) <=> ALL P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MEM] THEN
  ASM_MESON_TAC[]);;

let LENGTH_REPLICATE = prove
 (`!n x. LENGTH(REPLICATE n x) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; REPLICATE]);;

let EX_MAP = prove
 (`!P f l. EX P (MAP f l) <=> EX (P o f) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; EX; o_THM]);;

let EXISTS_EX = prove
 (`!P l. (?x. EX (P x) l) <=> EX (\s. ?x. P x s) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX] THEN
  ASM_MESON_TAC[]);;

let FORALL_ALL = prove
 (`!P l. (!x. ALL (P x) l) <=> ALL (\s. !x. P x s) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[]);;

let MEM_APPEND = prove
 (`!x l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \/ MEM x l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; APPEND; DISJ_ACI]);;

let MEM_MAP = prove
 (`!f y l. MEM y (MAP f l) <=> ?x. MEM x l /\ (y = f x)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MEM; MAP] THEN MESON_TAC[]);;

let FILTER_APPEND = prove
 (`!P l1 l2. FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let FILTER_MAP = prove
 (`!P f l. FILTER P (MAP f l) = MAP f (FILTER (P o f) l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; FILTER; o_THM] THEN COND_CASES_TAC THEN
  REWRITE_TAC[MAP]);;

let MEM_FILTER = prove
 (`!P l x. MEM x (FILTER P l) <=> P x /\ MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; FILTER] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

let EX_MEM = prove
 (`!P l. (?x. P x /\ MEM x l) <=> EX P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX; MEM] THEN
  ASM_MESON_TAC[]);;

let MAP_FST_ZIP = prove
 (`!l1 l2. (LENGTH l1 = LENGTH l2) ==> (MAP FST (ZIP l1 l2) = l1)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; SUC_INJ; MAP; FST; ZIP; NOT_SUC]);;

let MAP_SND_ZIP = prove
 (`!l1 l2. (LENGTH l1 = LENGTH l2) ==> (MAP SND (ZIP l1 l2) = l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; SUC_INJ; MAP; FST; ZIP; NOT_SUC]);;

let MEM_ASSOC = prove
 (`!l x. MEM (x,ASSOC x l) l <=> MEM x (MAP FST l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; MAP; ASSOC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PAIR; FST]);;

let ALL_APPEND = prove
 (`!P l1 l2. ALL P (APPEND l1 l2) <=> ALL P l1 /\ ALL P l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; APPEND; GSYM CONJ_ASSOC]);;

let MEM_EL = prove
 (`!l n. n < LENGTH l ==> MEM (EL n l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJUNCT1 LT; LENGTH] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; LT_SUC; TL]);;

let MEM_EXISTS_EL = prove
 (`!l x. MEM x l <=> ?i. i < LENGTH l /\ x = EL i l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; EL; MEM; CONJUNCT1 LT] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV
   [MESON[num_CASES] `(?i. P i) <=> P 0 \/ (?i. P(SUC i))`] THEN
  REWRITE_TAC[LT_SUC; LT_0; EL; HD; TL]);;

let ALL2_MAP2 = prove
 (`!l m. ALL2 P (MAP f l) (MAP g m) = ALL2 (\x y. P (f x) (g y)) l m`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP]);;

let AND_ALL2 = prove
 (`!P Q l m. ALL2 P l m /\ ALL2 Q l m <=> ALL2 (\x y. P x y /\ Q x y) l m`,
  GEN_TAC THEN GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[CONJ_ACI]);;

let ALL2_ALL = prove
 (`!P l. ALL2 P l l <=> ALL (\x. P x x) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL]);;

let APPEND_EQ_NIL = prove
 (`!l m. (APPEND l m = []) <=> (l = []) /\ (m = [])`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_APPEND; ADD_EQ_0]);;

let LENGTH_MAP2 = prove
 (`!f l m. (LENGTH l = LENGTH m) ==> (LENGTH(MAP2 f l m) = LENGTH m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_CONS_NIL; NOT_SUC; MAP2; SUC_INJ]);;

let MAP_EQ_NIL  = prove
 (`!f l. MAP f l = [] <=> l = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL]);;

let INJECTIVE_MAP = prove
 (`!f:A->B. (!l m. MAP f l = MAP f m ==> l = m) <=>
            (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[x:A]`; `[y:A]`]) THEN
    ASM_REWRITE_TAC[MAP; CONS_11];
    REPEAT LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
    ASM_MESON_TAC[]]);;

let SURJECTIVE_MAP = prove
 (`!f:A->B. (!m. ?l. MAP f l = m) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `y:B` THEN FIRST_X_ASSUM(MP_TAC o SPEC `[y:B]`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; CONS_11; NOT_CONS_NIL; MAP_EQ_NIL];
    MATCH_MP_TAC list_INDUCT] THEN
  ASM_MESON_TAC[MAP]);;

(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

let mk_cons h t =
  try let cons = mk_const("CONS",[type_of h,aty]) in
      mk_comb(mk_comb(cons,h),t)
  with Failure _ -> failwith "mk_cons";;

let mk_list (tms,ty) =
  try let nil = mk_const("NIL",[ty,aty]) in
      if tms = [] then nil else
      let cons = mk_const("CONS",[ty,aty]) in
      itlist (mk_binop cons) tms nil
  with Failure _ -> failwith "mk_list";;

let mk_flist tms =
  try mk_list(tms,type_of(hd tms))
  with Failure _ -> failwith "mk_flist";;

(* ------------------------------------------------------------------------- *)
(* Extra monotonicity theorems for inductive definitions.                    *)
(* ------------------------------------------------------------------------- *)

let MONO_ALL = prove
 (`(!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l`,
  DISCH_TAC THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

let MONO_ALL2 = prove
 (`(!x y. (P:A->B->bool) x y ==> Q x y) ==> ALL2 P l l' ==> ALL2 Q l l'`,
  DISCH_TAC THEN
  SPEC_TAC(`l':B list`,`l':B list`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2_DEF] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

monotonicity_theorems := [MONO_ALL; MONO_ALL2] @ !monotonicity_theorems;;

(* ------------------------------------------------------------------------- *)
(* Apply a conversion down a list.                                           *)
(* ------------------------------------------------------------------------- *)

let rec LIST_CONV conv tm =
  if is_cons tm then
    COMB2_CONV (RAND_CONV conv) (LIST_CONV conv) tm
  else if fst(dest_const tm) = "NIL" then REFL tm
  else failwith "LIST_CONV";;

(* ------------------------------------------------------------------------- *)
(* Type of characters, like the HOL88 "ascii" type.                          *)
(* ------------------------------------------------------------------------- *)

let char_INDUCT,char_RECURSION = define_type
 "char = ASCII bool bool bool bool bool bool bool bool";;

new_type_abbrev("string",`:char list`);;
