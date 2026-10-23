(* ========================================================================= *)
(* 4CT/quiz.ml                                                               *)
(*                                                                           *)
(* quiz.v: quizzes, quiz embeddings and the quiz pre-embedding theorem.      *)
(*                                                                           *)
(* A quiz is a pair of question trees walked from a dart x0 and its edge     *)
(* mate; each node records the arity of the dart reached by L/R steps        *)
(* (qstepL = node o edge o node, qstepR = node o edge) and fitq/fitqz say    *)
(* that the recorded arities match.  A quiz valid for a configuration Gc     *)
(* (valid_quiz: both questions start with QaskR, it fits at x0c, its walk    *)
(* s0c is face-simple and its band is the kernel) that also fits a plain     *)
(* cubic map Gm at x0m yields the pre-embedding embedqz : Gc -> Gm sending   *)
(* the i-th dart of s0c to the i-th dart of s0m (QUIZ_PREEMBEDDING).         *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/coloring.ml";;
needs "4CT/jordan.ml";;
needs "4CT/preembedding.ml";;
needs "4CT/embed_prelim.ml";;
needs "4CT/cfmap.ml";;
needs "4CT/part_mirror.ml";;

(* ------------------------------------------------------------------------- *)
(* Arities, questions, quizzes and their walks (quiz.v).                     *)
(* ------------------------------------------------------------------------- *)

let qarity_INDUCT,qarity_RECURSION = define_type
  "qarity = Qa5 | Qa6 | Qa7 | Qa8 | Qa9 | Qa10 | Qa11";;
let nat_of_qarity = new_recursive_definition qarity_RECURSION
 `(nat_of_qarity Qa5 = 5) /\ (nat_of_qarity Qa6 = 6) /\
  (nat_of_qarity Qa7 = 7) /\
  (nat_of_qarity Qa8 = 8) /\ (nat_of_qarity Qa9 = 9) /\
  (nat_of_qarity Qa10 = 10) /\
  (nat_of_qarity Qa11 = 11)`;;
let qarity_of_nat = new_definition
 `qarity_of_nat n =
    if n = 5 then Qa5 else if n = 6 then Qa6 else if n = 7 then Qa7 else
    if n = 8 then Qa8 else if n = 9 then Qa9 else if n = 10 then Qa10
    else Qa11`;;
let question_INDUCT,question_RECURSION = define_type
  "question = Qask0
            | Qask1 qarity
            | QaskL qarity question
            | QaskR qarity question
            | QaskLR qarity question question
            | QaskLL qarity question
            | QaskRR qarity question";;
let isQaskR = new_recursive_definition question_RECURSION
 `(isQaskR Qask0 = F) /\ (isQaskR (Qask1 qa) = F) /\
  (isQaskR (QaskL qa ql) = F) /\ (isQaskR (QaskR qa qr) = T) /\
  (isQaskR (QaskLR qa ql qr) = F) /\ (isQaskR (QaskLL qa qll) = F) /\
  (isQaskR (QaskRR qa qrr) = F)`;;
let flatq = new_recursive_definition question_RECURSION
 `(flatq Qask0 = []) /\
  (flatq (Qask1 qa) = [nat_of_qarity qa]) /\
  (flatq (QaskL qa ql) = CONS (nat_of_qarity qa) (flatq ql)) /\
  (flatq (QaskR qa qr) = CONS (nat_of_qarity qa) (flatq qr)) /\
  (flatq (QaskLR qa ql qr) =
  CONS (nat_of_qarity qa) (APPEND (flatq ql) (flatq qr))) /\
  (flatq (QaskLL qa qll) = CONS (nat_of_qarity qa) (flatq qll)) /\
  (flatq (QaskRR qa qrr) = CONS (nat_of_qarity qa) (flatq qrr))`;;
let flipq = new_recursive_definition question_RECURSION
 `(flipq Qask0 = Qask0) /\
  (flipq (Qask1 qa) = Qask1 qa) /\
  (flipq (QaskL qa ql) = QaskR qa (flipq ql)) /\
  (flipq (QaskR qa qr) = QaskL qa (flipq qr)) /\
  (flipq (QaskLR qa ql qr) = QaskLR qa (flipq qr) (flipq ql)) /\
  (flipq (QaskLL qa qll) = QaskRR qa (flipq qll)) /\
  (flipq (QaskRR qa qrr) = QaskLL qa (flipq qrr))`;;
let qstepL = new_definition
 `qstepL (H:(A)hypermap) x = node_map H (edge_map H (node_map H x))`;;
let qstepR = new_definition
 `qstepR (H:(A)hypermap) x = node_map H (edge_map H x)`;;
let quiz_INDUCT,quiz_RECURSION = define_type "quiz = Quiz question question";;
let isQuizR = new_recursive_definition quiz_RECURSION
 `isQuizR (Quiz q0 q1) = (isQaskR q0 /\ isQaskR q1)`;;
let flatqz = new_recursive_definition quiz_RECURSION
 `flatqz (Quiz q0 q1) = APPEND (flatq q0) (flatq q1)`;;
let qra = new_recursive_definition question_RECURSION
 `(qra Qask0 = Qa5) /\ (qra (Qask1 qa) = qa) /\ (qra (QaskL qa ql) = qa) /\
  (qra (QaskR qa qr) = qa) /\ (qra (QaskLR qa ql qr) = qa) /\
  (qra (QaskLL qa qll) = qa) /\ (qra (QaskRR qa qrr) = qa)`;;
let qrb = new_recursive_definition question_RECURSION
 `(qrb Qask0 = Qask0) /\ (qrb (Qask1 qa) = Qask0) /\
  (qrb (QaskL qa ql) = ql) /\
  (qrb (QaskR qa qr) = qr) /\ (qrb (QaskLR qa ql qr) = ql) /\
  (qrb (QaskLL qa qll) = qll) /\ (qrb (QaskRR qa qrr) = qrr)`;;
let flipqz = new_recursive_definition quiz_RECURSION
 `flipqz (Quiz q0 q1) =
    if isQaskR q0 /\ isQaskR q1
    then Quiz (QaskR (qra q0) (flipq (qrb q1)))
    (QaskR (qra q1) (flipq (qrb q0)))
    else Quiz q0 q1`;;
let walkq = new_recursive_definition question_RECURSION
 `(walkq Qask0 (H:(A)hypermap) (x:A) = []) /\
  (walkq (Qask1 qa) H x = [x]) /\
  (walkq (QaskL qa ql) H x = CONS x (walkq ql H (qstepL H x))) /\
  (walkq (QaskR qa qr) H x = CONS x (walkq qr H (qstepR H x))) /\
  (walkq (QaskLR qa ql qr) H x =
     CONS x (APPEND (walkq ql H (qstepL H x)) (walkq qr H (qstepR H x)))) /\
  (walkq (QaskLL qa qll) H x =
     CONS (edge_map H (node_map H (qstepL H x)))
     (walkq qll H (qstepL H (qstepL H x)))) /\
  (walkq (QaskRR qa qrr) H x =
     CONS (qstepR H x) (walkq qrr H (qstepR H (qstepR H x))))`;;
let fitq = new_definition
 `fitq (H:(A)hypermap) (x:A) q <=> flatq q = MAP (arity H) (walkq q H x)`;;
let walkqz = new_recursive_definition quiz_RECURSION
 `walkqz (Quiz q0 q1) (H:(A)hypermap) (x:A) =
    APPEND (walkq q0 H x) (walkq q1 H (edge_map H x))`;;
let fitqz = new_definition
 `fitqz (H:(A)hypermap) (x:A) qz <=>
  flatqz qz = MAP (arity H) (walkqz qz H x)`;;
(* Position of y in the face_map-orbit of x, first index satisfying p in     *)
(* a list, and the i-th element of a list with default x0 (Coq findex, find, *)
(* nth).  The last two are total: embedqz needs no range side conditions.    *)
let findex = new_definition
  `findex (f:A->A) x y = minimal n. ITER n f x = y`;;
let findp = define
  `(findp (p:A->bool) [] = 0) /\
   (findp p (CONS h t) = (if p h then 0 else SUC(findp p t)))`;;
let nthd = define
  `(nthd (x0:A) [] i = x0) /\
   (nthd (x0:A) (CONS h t) i = (if i = 0 then h else nthd x0 t (i - 1)))`;;
let valid_quiz = new_definition
  `valid_quiz (Gc:(A)hypermap) rc (x0c:A) qz <=>
     isQuizR qz /\ fitqz Gc x0c qz /\ face_simple Gc (walkqz qz Gc x0c) /\
     (!x. fband Gc (walkqz qz Gc x0c) x <=> kernel Gc rc x)`;;
let embedqz = new_definition
  `embedqz (Gm:(B)hypermap) (Gc:(A)hypermap) (x0m:B) (x0c:A)
   (qz:quiz) (x:A) : B =
     ITER (findex (face_map Gc)
                  (nthd x0c (walkqz qz Gc x0c)
                  (findp (\z. cface Gc x z) (walkqz qz Gc x0c))) x)
          (face_map Gm)
          (nthd x0m (walkqz qz Gm x0m)
                    (findp (\z. cface Gc x z) (walkqz qz Gc x0c)))`;;

(* ------------------------------------------------------------------------- *)
(* Sizes, splitting a fit, dart preservation, and the mirror lemma           *)
(* fitqz_flip (quiz.v FitQuiz section).                                      *)
(* ------------------------------------------------------------------------- *)

let SIZE_WALKQ = prove
 (`!q (H:(A)hypermap) (x:A). LENGTH(walkq q H x) = LENGTH(flatq q)`,
  MATCH_MP_TAC question_INDUCT THEN
  REWRITE_TAC[walkq; flatq; LENGTH; LENGTH_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SIZE_WALKQZ = prove
 (`!qz (H:(A)hypermap) (x:A). LENGTH(walkqz qz H x) = LENGTH(flatqz qz)`,
  MATCH_MP_TAC quiz_INDUCT THEN
  REWRITE_TAC[walkqz; flatqz; LENGTH_APPEND; SIZE_WALKQ]);;

let FITQ_CAT = prove
 (`!q (H:(A)hypermap) (x:A) sa s.
     APPEND (flatq q) sa = MAP (arity H) (APPEND (walkq q H x) s) <=>
     fitq H x q /\ sa = MAP (arity H) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_APPEND; fitq] THEN
  MATCH_MP_TAC APPEND_EQ_SPLIT THEN REWRITE_TAC[LENGTH_MAP; SIZE_WALKQ]);;

let QSTEP_IN_DART = prove
 (`!(G:(A)hypermap) x. x IN dart G
     ==> qstepL G x IN dart G /\ qstepR G x IN dart G`,
  SIMP_TAC[qstepL; qstepR; NODE_MAP_IN_DART; EDGE_MAP_IN_DART]);;

let WALKQ_MEM_DART = prove
 (`!q (H:(A)hypermap) x. x IN dart H ==> ALL (\z. z IN dart H) (walkq q H x)`,
  MATCH_MP_TAC question_INDUCT THEN
  REWRITE_TAC[walkq; ALL; ALL_APPEND] THEN
  SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; QSTEP_IN_DART]);;

let WALKQZ_MEM_DART = prove
 (`!qz (H:(A)hypermap) x.
     x IN dart H ==> ALL (\z. z IN dart H) (walkqz qz H x)`,
  MATCH_MP_TAC quiz_INDUCT THEN
  SIMP_TAC[walkqz; ALL_APPEND; WALKQ_MEM_DART; EDGE_MAP_IN_DART]);;

let QSTEP_MIRROR = prove
 (`!(G:(A)hypermap) x. plain_hypermap G /\ cubic_hypermap G /\ x IN dart G
     ==> qstepL (mirror G) x = qstepR G x /\
         qstepR (mirror G) x = qstepL G x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[qstepL; qstepR; MIRROR_COMPONENTS; o_THM] THEN
  ASM_SIMP_TAC[FEF_NE; NODE_MAP_IN_DART; FACE_MAP_IN_DART; EDGE_MAP_IN_DART;
               CFT_PLAIN_NF; CFT_PLAIN_EE]);;

let FIT_FLIP = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G
    ==> !q (x:A). x IN dart G
                  ==> (fitq G x (flipq q) <=> fitq (mirror G) x q)`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC question_INDUCT THEN
  REWRITE_TAC[flipq; fitq; flatq; walkq; MAP; CONS_11] THEN
  REWRITE_TAC[GSYM MAP_APPEND; GSYM fitq; FITQ_CAT] THEN
  REWRITE_TAC[GSYM fitq] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[QSTEP_MIRROR; ARITY_MIRROR; ARITY_EN; QSTEP_IN_DART;
               DART_MIRROR; EDGE_MAP_IN_DART; NODE_MAP_IN_DART] THEN
  REWRITE_TAC[CONJ_ACI]);;

let FITQZ_FLIP = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G
    ==> !qz (x:A). isQuizR qz /\ x IN dart G
        ==> (fitqz G x (flipqz qz) <=> fitqz (mirror G) (face_map G x) qz)`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC quiz_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`q0:question`; `q1:question`] THEN GEN_TAC THEN
  REWRITE_TAC[isQuizR] THEN
  STRUCT_CASES_TAC(ISPEC `q0:question` (cases "question")) THEN
  REWRITE_TAC[isQaskR] THEN
  STRUCT_CASES_TAC(ISPEC `q1:question` (cases "question")) THEN
  REWRITE_TAC[isQaskR] THEN DISCH_TAC THEN
  SUBGOAL_THEN `face_map G (x:A) IN dart G /\ edge_map G x IN dart G /\
                face_map G (edge_map G x) IN dart G` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART]; ALL_TAC] THEN
  REWRITE_TAC[flipqz; isQaskR; qra; qrb; fitqz; flatqz; walkqz; flatq; walkq;
              APPEND; MAP; CONS_11] THEN
  REWRITE_TAC[GSYM MAP_APPEND; FITQ_CAT] THEN
  REWRITE_TAC[GSYM fitq; MAP; CONS_11] THEN REWRITE_TAC[GSYM fitq] THEN
  ASM_SIMP_TAC[ARITY_MIRROR; EDGE_MIRROR_FACE; QSTEP_MIRROR; ARITY_FACE;
               FACE_MAP_IN_DART; EDGE_MAP_IN_DART] THEN
  REWRITE_TAC[qstepL; qstepR] THEN
  ASM_SIMP_TAC[PLAIN_EQ; PLAIN_EQ'; EDGE_MAP_IN_DART; FACE_MAP_IN_DART] THEN
  ASM_SIMP_TAC[FIT_FLIP; NODE_MAP_IN_DART; EDGE_MAP_IN_DART] THEN
  REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* The index functions: findex in a face orbit, findp / nthd on lists.       *)
(* ------------------------------------------------------------------------- *)

let FINDEX0 = prove
 (`!(f:A->A) x. findex f x x = 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[findex] THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN REWRITE_TAC[ITER; LT]);;

let ITER_FINDEX = prove
 (`!(f:A->A) x y. (?n. ITER n f x = y) ==> ITER (findex f x y) f x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[findex] THEN
  MP_TAC(ISPEC `\n. ITER n (f:A->A) x = y` MINIMAL) THEN SIMP_TAC[]);;

let CFACE_ITER_FINDEX = prove
 (`!(H:(A)hypermap) x y. cface H x y
     ==> ITER (findex (face_map H) x y) (face_map H) x = y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ITER_FINDEX THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN
  MESON_TAC[]);;

let FINDEX_LT_ARITY = prove
 (`!(H:(A)hypermap) x y. x IN dart H /\ cface H x y
     ==> findex (face_map H) x y < arity H x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`;
                 `y:A`] ORBIT_INDEX) THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES; GSYM face; GSYM cface;
                  GSYM arity] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE `!j. ~(j < k) /\ j < a ==> k < a`) THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[findex] THEN
  MP_TAC(ISPEC `\n. ITER n (face_map (H:(A)hypermap)) x = y` MINIMAL) THEN
  ASM_MESON_TAC[]);;

let FINDEX_ITER = prove
 (`!(H:(A)hypermap) x n. x IN dart H /\ n < arity H x
     ==> findex (face_map H) x (ITER n (face_map H) x) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[findex] THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m:num = n` (fun th -> ASM_MESON_TAC[th; LT_REFL]) THEN
  MATCH_MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `x:A`;
                       `arity (H:(A)hypermap) x`] ORBIT_ITER_DISTINCT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(MATCH_MP PERMUTES_INJECTIVE
             (ISPEC `H:(A)hypermap` FACE_MAP_PERMUTES)) THEN SIMP_TAC[];
    MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
                  ORBIT_SIZE_DIVIDES) THEN
    ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES; GSYM arity];
    ASM_MESON_TAC[LT_TRANS]]);;

let HAS_FINDP = prove
 (`!p (s:(A)list). EX p s <=> findp p s < LENGTH s`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[findp; LENGTH; EX] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FINDP_NTHD = prove
 (`!p (x0:A) s. EX p s ==> p (nthd x0 s (findp p s))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[EX; findp] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[nthd; NOT_SUC; SUC_SUB1] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let NTHD_EL = prove
 (`!(x0:A) s i. i < LENGTH s ==> nthd x0 s i = EL i s`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[nthd; EL; HD; TL; LENGTH; NOT_SUC; SUC_SUB1; LT_SUC; LT_0;
               CONJUNCT1 LT]);;

let MEM_NTHD = prove
 (`!(x0:A) s i. i < LENGTH s ==> MEM (nthd x0 s i) s`,
  SIMP_TAC[NTHD_EL] THEN MESON_TAC[MEM_EXISTS_EL]);;

let NTHD_DEFAULT = prove
 (`!(x0:A) s i. LENGTH s <= i ==> nthd x0 s i = x0`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[nthd; LENGTH] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[NOT_SUC; SUC_SUB1; LE_SUC; LE]);;

let NTHD_APPEND_LEN = prove
 (`!(x0:A) l1 l2. nthd x0 (APPEND l1 l2) (LENGTH l1) = nthd x0 l2 0`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; nthd; NOT_SUC; SUC_SUB1]);;

(* In a face-simple list the first dart cofacial with the i-th one is the    *)
(* i-th one (Coq simple_uniq + index_uniq).                                  *)

let FINDP_SIMPLE = prove
 (`!(H:(A)hypermap) (x0:A) s i.
     face_simple H s /\ i < LENGTH s
     ==> findp (\z. cface H (nthd x0 s i) z) s = i`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; face_simple] THEN
  INDUCT_TAC THEN REWRITE_TAC[nthd; findp; NOT_SUC; SUC_SUB1; LT_SUC] THEN
  REWRITE_TAC[CFACE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~cface H (nthd (x0:A) t i) h` (fun th -> ASM_SIMP_TAC[th]) THEN
  UNDISCH_TAC `~fband H (t:(A)list) h` THEN
  REWRITE_TAC[CONTRAPOS_THM; FBAND_MEM_IFF] THEN
  ASM_MESON_TAC[MEM_NTHD; CFACE_SYM_GEN]);;

(* ------------------------------------------------------------------------- *)
(* The quiz embedding h = embedqz Gm Gc x0m x0c qz (quiz.v QuizEmbedding):   *)
(* h maps the i-th dart of s0c = walkqz qz Gc x0c to the i-th dart of        *)
(* s0m = walkqz qz Gm x0m and is a face morphism on the kernel.              *)
(* ------------------------------------------------------------------------- *)

let NTHD_WALKQZ_DART = prove
 (`!qz (H:(A)hypermap) x0 i.
     x0 IN dart H /\ i < LENGTH (walkqz qz H x0)
     ==> nthd x0 (walkqz qz H x0) i IN dart H`,
  MESON_TAC[WALKQZ_MEM_DART; ALL_MEM_D; MEM_NTHD]);;

let EMBEDQZ_IN_DART = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c qz x.
     x0m IN dart Gm ==> embedqz Gm Gc x0m x0c qz x IN dart Gm`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[embedqz] THEN
  MATCH_MP_TAC ITER_PERMUTES_IN THEN ASM_REWRITE_TAC[FACE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[NTHD_WALKQZ_DART; NTHD_DEFAULT; NOT_LT]);;

(* The index of a kernel dart x in s0c, and the arities along s0c and s0m.   *)

let EMBEDQZ_INDEX = prove
 (`!(Gc:(A)hypermap) x0c rc qz x.
     valid_quiz Gc rc x0c qz /\ kernel Gc rc x
     ==> findp (\z. cface Gc x z) (walkqz qz Gc x0c) <
         LENGTH (walkqz qz Gc x0c) /\
         cface Gc x (nthd x0c (walkqz qz Gc x0c)
                          (findp (\z. cface Gc x z) (walkqz qz Gc x0c)))`,
  REWRITE_TAC[valid_quiz] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. cface (Gc:(A)hypermap) x z`; `x0c:A`;
                 `walkqz qz (Gc:(A)hypermap) x0c`] FINDP_NTHD) THEN
  REWRITE_TAC[GSYM HAS_FINDP; GSYM fband] THEN ASM_MESON_TAC[]);;

let ARITY_NTHD_WALKQZ = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz i.
     valid_quiz Gc rc x0c qz /\ fitqz Gm x0m qz /\
     i < LENGTH (walkqz qz Gc x0c)
     ==> arity Gm (nthd x0m (walkqz qz Gm x0m) i) =
         arity Gc (nthd x0c (walkqz qz Gc x0c) i)`,
  REWRITE_TAC[valid_quiz; fitqz] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH (walkqz qz (Gm:(B)hypermap) x0m)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SIZE_WALKQZ] THEN ASM_MESON_TAC[SIZE_WALKQZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[NTHD_EL; GSYM EL_MAP] THEN ASM_MESON_TAC[]);;

(* Coq Dhx0, Dhs0, Dhex0: h x0c = x0m, h s0c[i] = s0m[i], h (edge x0c) =     *)
(* edge x0m.                                                                 *)

let DHX0 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz.
     valid_quiz Gc rc x0c qz ==> embedqz Gm Gc x0m x0c qz x0c = x0m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_quiz] THEN
  STRUCT_CASES_TAC(ISPEC `qz:quiz` (cases "quiz")) THEN
  REWRITE_TAC[isQuizR] THEN STRIP_TAC THEN UNDISCH_TAC `isQaskR a0` THEN
  STRUCT_CASES_TAC(ISPEC `a0:question` (cases "question")) THEN
  REWRITE_TAC[isQaskR; embedqz; walkqz; walkq; APPEND; findp; CFACE_REFL;
              nthd; FINDEX0; ITER]);;

let DHS0 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c (rc:(A)list) qz i.
     valid_quiz Gc rc x0c qz
     ==> embedqz Gm Gc x0m x0c qz (nthd x0c (walkqz qz Gc x0c) i) =
         nthd x0m (walkqz qz Gm x0m) i`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i < LENGTH (walkqz qz (Gc:(A)hypermap) x0c)` THENL
   [REWRITE_TAC[embedqz] THEN
    SUBGOAL_THEN
     `findp (\z. cface (Gc:(A)hypermap) (nthd (x0c:A) (walkqz qz Gc x0c) i) z)
            (walkqz qz Gc x0c) = i`
     SUBST1_TAC THENL
     [MATCH_MP_TAC FINDP_SIMPLE THEN ASM_MESON_TAC[valid_quiz];
      REWRITE_TAC[FINDEX0; ITER]];
    SUBGOAL_THEN `LENGTH (walkqz qz (Gm:(B)hypermap) x0m) <= i /\
                  LENGTH (walkqz qz (Gc:(A)hypermap) x0c) <= i`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SIZE_WALKQZ; NOT_LT]; ASM_SIMP_TAC[NTHD_DEFAULT]] THEN
    ASM_MESON_TAC[DHX0]]);;

let DHEX0 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz.
     valid_quiz Gc rc x0c qz
     ==> embedqz Gm Gc x0m x0c qz (edge_map Gc x0c) = edge_map Gm x0m`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `qz:quiz` (cases "quiz")) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `LENGTH (walkq a0 (Gc:(A)hypermap) x0c)` o
    MATCH_MP (ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `x0m:B`; `x0c:A`]
                     DHS0)) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[valid_quiz; isQuizR] THEN
  STRUCT_CASES_TAC(ISPEC `a1:question` (cases "question")) THEN
  REWRITE_TAC[isQaskR] THEN STRIP_TAC THEN
  REWRITE_TAC[walkqz; NTHD_APPEND_LEN; walkq; nthd] THEN
  SUBGOAL_THEN `LENGTH (walkq a0 (Gc:(A)hypermap) x0c) =
                LENGTH (walkq a0 (Gm:(B)hypermap) x0m)`
    SUBST1_TAC THENL [REWRITE_TAC[SIZE_WALKQ]; ALL_TAC] THEN
  REWRITE_TAC[NTHD_APPEND_LEN; walkq; nthd]);;

(* Coq embedqz_arity and embedqz_face: h preserves arities and commutes with *)
(* face_map on the kernel.                                                   *)

let EMBEDQZ_ARITY = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz x.
     valid_quiz Gc rc x0c qz /\ fitqz Gm x0m qz /\
     x0c IN dart Gc /\ x0m IN dart Gm /\ kernel Gc rc x
     ==> arity Gm (embedqz Gm Gc x0m x0c qz x) = arity Gc x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `x0c:A`; `rc:(A)list`; `qz:quiz`; `x:A`]
                EMBEDQZ_INDEX) THEN
  ASM_REWRITE_TAC[embedqz] THEN
  ABBREV_TAC `i = findp (\z. cface (Gc:(A)hypermap) x z) (walkqz qz Gc x0c)`
  THEN STRIP_TAC THEN
  SUBGOAL_THEN `nthd x0m (walkqz qz (Gm:(B)hypermap) x0m) i IN dart Gm`
    ASSUME_TAC THENL
   [MATCH_MP_TAC NTHD_WALKQZ_DART THEN ASM_MESON_TAC[SIZE_WALKQZ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITY_ITER_FACE] THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `x0m:B`; `x0c:A`;
                 `rc:(A)list`; `qz:quiz`; `i:num`] ARITY_NTHD_WALKQZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC ARITY_CFACE THEN ASM_MESON_TAC[kernel]);;

let EMBEDQZ_FACE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz x.
     valid_quiz Gc rc x0c qz /\ fitqz Gm x0m qz /\
     x0c IN dart Gc /\ x0m IN dart Gm /\ kernel Gc rc x
     ==> embedqz Gm Gc x0m x0c qz (face_map Gc x) =
         face_map Gm (embedqz Gm Gc x0m x0c qz x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `x0c:A`; `rc:(A)list`; `qz:quiz`; `x:A`]
                EMBEDQZ_INDEX) THEN
  ASM_REWRITE_TAC[embedqz; CFACE_FACE_L] THEN
  ABBREV_TAC `i = findp (\z. cface (Gc:(A)hypermap) x z) (walkqz qz Gc x0c)`
  THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `x0m:B`; `x0c:A`;
                 `rc:(A)list`; `qz:quiz`; `i:num`] ARITY_NTHD_WALKQZ) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `yc = nthd x0c (walkqz qz (Gc:(A)hypermap) x0c) i` THEN
  ABBREV_TAC `sm = nthd x0m (walkqz qz (Gm:(B)hypermap) x0m) i` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(yc:A) IN dart Gc /\ (sm:B) IN dart Gm` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["yc"; "sm"] THEN CONJ_TAC THEN
    MATCH_MP_TAC NTHD_WALKQZ_DART THEN ASM_MESON_TAC[SIZE_WALKQZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `cface (Gc:(A)hypermap) yc x` ASSUME_TAC THENL
   [ASM_MESON_TAC[CFACE_SYM_GEN]; ALL_TAC] THEN
  ABBREV_TAC `j = findex (face_map (Gc:(A)hypermap)) yc x` THEN
  SUBGOAL_THEN `x = ITER j (face_map (Gc:(A)hypermap)) yc` SUBST1_TAC THENL
   [ASM_MESON_TAC[CFACE_ITER_FINDEX]; ALL_TAC] THEN
  SUBGOAL_THEN `j < arity (Gc:(A)hypermap) yc` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINDEX_LT_ARITY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN
  ASM_CASES_TAC `SUC j < arity (Gc:(A)hypermap) yc` THEN
  ASM_SIMP_TAC[FINDEX_ITER] THEN
  SUBGOAL_THEN `SUC j = arity (Gc:(A)hypermap) yc` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[ITER_FACE_ARITY; FINDEX0; ITER]] THEN
  ASM_MESON_TAC[ITER_FACE_ARITY]);;

(* ------------------------------------------------------------------------- *)
(* Edge-centrality along the quiz walks (Coq embedqz_central).  The core is  *)
(* HC_WALK, stated for any h : A -> B that commutes with face_map on the     *)
(* kernel; the hypermap identities it needs come first.  Throughout,         *)
(* edge_map o node_map is the inverse of face_map (nodeK).                   *)
(* ------------------------------------------------------------------------- *)

let KERNEL_FACE_MAP_EQ = prove
 (`!(H:(A)hypermap) p x. kernel H p (face_map H x) <=> kernel H p x`,
  SIMP_TAC[kernel; FBAND_FACE_MAP_EQ; PERMUTES_IN_IMAGE; FACE_MAP_PERMUTES]);;

let KERNEL_EN_EQ = prove
 (`!(H:(A)hypermap) p x.
     kernel H p (edge_map H (node_map H x)) <=> kernel H p x`,
  MESON_TAC[KERNEL_FACE_MAP_EQ; nodeK]);;

let FBAND_EN_EQ = prove
 (`!(H:(A)hypermap) p x.
     fband H p (edge_map H (node_map H x)) <=> fband H p x`,
  MESON_TAC[FBAND_FACE_MAP_EQ; nodeK]);;

let CFACE_EN_EQ = prove
 (`!(H:(A)hypermap) y z.
     (cface H (edge_map H (node_map H y)) z <=> cface H y z) /\
     (cface H z (edge_map H (node_map H y)) <=> cface H z y)`,
  MESON_TAC[CFACE_FACE_L; CFACE_SYM_GEN; nodeK]);;

let KERNEL_N3 = prove
 (`!(H:(A)hypermap) rc x. quasicubic H (set_of_list rc) /\ kernel H rc x
     ==> node_map H (node_map H (node_map H x)) = x`,
  REWRITE_TAC[kernel] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC QUASICUBIC_EQ THEN EXISTS_TAC `set_of_list(rc:(A)list)` THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN ASM_MESON_TAC[FBAND_MEM]);;

let KERNEL_NN = prove
 (`!(H:(A)hypermap) rc x. quasicubic H (set_of_list rc) /\ kernel H rc x
     ==> node_map H (node_map H x) = face_map H (edge_map H x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP PERMUTES_INJECTIVE (ISPEC `H:(A)hypermap` NODE_MAP_PERMUTES))
  THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
  REWRITE_TAC[edgeK] THEN MATCH_MP_TAC KERNEL_N3 THEN
  EXISTS_TAC `rc:(A)list` THEN ASM_REWRITE_TAC[]);;

let KERNEL_NN_EQ = prove
 (`!(H:(A)hypermap) rc x. quasicubic H (set_of_list rc) /\ kernel H rc x
     ==> (kernel H rc (node_map H (node_map H x)) <=>
          kernel H rc (edge_map H x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rc:(A)list`; `x:A`] KERNEL_NN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[KERNEL_FACE_MAP_EQ]);;

let CUBIC_NN = prove
 (`!(H:(A)hypermap) x. cubic_hypermap H
     ==> node_map H (node_map H x) = face_map H (edge_map H x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP PERMUTES_INJECTIVE (ISPEC `H:(A)hypermap` NODE_MAP_PERMUTES))
  THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
  ASM_SIMP_TAC[edgeK; CUBIC_EQ_U]);;

(* The QaskLL head: node(node(edge(node(node x)))) = face(face(edge x)) on   *)
(* both maps (Coq's n3c/n3m chains).                                         *)

let CUBIC_NN_EN_NN = prove
 (`!(H:(A)hypermap) x. plain_hypermap H /\ cubic_hypermap H
     ==> node_map H (node_map H (edge_map H (node_map H (node_map H x)))) =
         face_map H (face_map H (edge_map H x))`,
  SIMP_TAC[CUBIC_NN; CFT_PLAIN_EE]);;

let KERNEL_NN_EN_NN = prove
 (`!(H:(A)hypermap) rc x.
     plain_hypermap H /\ quasicubic H (set_of_list rc) /\
     kernel H rc x /\ kernel H rc (edge_map H x)
     ==> node_map H (node_map H (edge_map H (node_map H (node_map H x)))) =
         face_map H (face_map H (edge_map H x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rc:(A)list`;
                 `face_map H (face_map H (edge_map H (x:A)))`] KERNEL_N3) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rc:(A)list`; `x:A`] KERNEL_NN) THEN
  ASM_REWRITE_TAC[KERNEL_FACE_MAP_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `edge_map H (face_map H (edge_map H (x:A))) =
    node_map H (face_map H (face_map H (edge_map H x)))`
    SUBST1_TAC THENL [ASM_SIMP_TAC[CFT_PLAIN_NF]; DISCH_THEN ACCEPT_TAC]);;

let HC_FINV = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc (h:A->B).
     (!x. kernel Gc rc x ==> h (face_map Gc x) = face_map Gm (h x))
     ==> !x. kernel Gc rc x
             ==> h (edge_map Gc (node_map Gc x)) =
                 edge_map Gm (node_map Gm (h x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP PERMUTES_INJECTIVE
           (ISPEC `Gm:(B)hypermap` FACE_MAP_PERMUTES)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `edge_map Gc (node_map Gc (x:A))`) THEN
  ASM_REWRITE_TAC[KERNEL_EN_EQ; nodeK] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let HC_NN = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc (h:A->B).
     quasicubic Gc (set_of_list rc) /\ cubic_hypermap Gm /\
     (!x. kernel Gc rc x ==> h (face_map Gc x) = face_map Gm (h x))
     ==> !x. kernel Gc rc x /\ kernel Gc rc (edge_map Gc x) /\
             h (edge_map Gc x) = edge_map Gm (h x)
             ==> h (node_map Gc (node_map Gc x)) =
                 node_map Gm (node_map Gm (h x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x:A`] KERNEL_NN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[CUBIC_NN]);;

let WALKQ_APPEND_EQ = prove
 (`!q (Gc:(A)hypermap) (Gm:(B)hypermap) (h:A->B) x y l m.
     APPEND (MAP h (walkq q Gc x)) l = APPEND (walkq q Gm y) m <=>
     MAP h (walkq q Gc x) = walkq q Gm y /\ l = m`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC APPEND_EQ_SPLIT THEN
  REWRITE_TAC[LENGTH_MAP; SIZE_WALKQ]);;

(* Coq hc_walk: if x and edge x are kernel darts, x is edge-central and h    *)
(* maps the walk of q from node x onto the walk from node (h x), with all    *)
(* its darts in the kernel, then every dart of the walk is edge-central.     *)
(* The seven cases are closed by one tactic: unfold the head, apply the      *)
(* induction hypothesis to the tail, and simplify with the identities above. *)

let HC_WALK = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc (h:A->B).
     plain_hypermap Gc /\ quasicubic Gc (set_of_list rc) /\
     plain_hypermap Gm /\ cubic_hypermap Gm /\
     (!x. kernel Gc rc x ==> h (face_map Gc x) = face_map Gm (h x))
     ==> !q x. kernel Gc rc x /\ kernel Gc rc (edge_map Gc x) /\
               h (edge_map Gc x) = edge_map Gm (h x) /\
               ALL (kernel Gc rc) (walkq q Gc (node_map Gc x)) /\
               MAP h (walkq q Gc (node_map Gc x)) =
               walkq q Gm (node_map Gm (h x))
               ==> ALL (edge_central Gc Gm h) (walkq q Gc (node_map Gc x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`]
                HC_NN) THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`]
                HC_FINV) THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] KERNEL_NN_EN_NN) THEN
  MP_TAC(ISPEC `Gm:(B)hypermap` CUBIC_NN_EN_NN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC question_INDUCT THEN
  REWRITE_TAC[walkq; ALL; MAP; CONS_11; qstepL; qstepR; ALL_APPEND;
              MAP_APPEND; WALKQ_APPEND_EQ] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[edge_central] THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_SIMP_TAC[KERNEL_FACE_MAP_EQ; KERNEL_EN_EQ; KERNEL_NN_EQ; CFT_PLAIN_EE]);;

(* Coq embedqz_central: every dart of s0c is edge-central.  A valid quiz has *)
(* the form Quiz (QaskR qa0 q01) (QaskR qa1 q10), so s0c = x0c :: walkq q01  *)
(* (node (edge x0c)) ++ edge x0c :: walkq q10 (node (edge (edge x0c))) and   *)
(* HC_WALK applies to the two tails.                                         *)

let ISQUIZR_STRUCT = prove
 (`!(Gc:(A)hypermap) rc x0c qz.
     valid_quiz Gc rc x0c qz
     ==> ?qa0 q01 qa1 q10. qz = Quiz (QaskR qa0 q01) (QaskR qa1 q10)`,
  REWRITE_TAC[valid_quiz] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  STRUCT_CASES_TAC(ISPEC `qz:quiz` (cases "quiz")) THEN
  REWRITE_TAC[isQuizR] THEN
  STRUCT_CASES_TAC(ISPEC `a0:question` (cases "question")) THEN
  REWRITE_TAC[isQaskR] THEN
  STRUCT_CASES_TAC(ISPEC `a1:question` (cases "question")) THEN
  REWRITE_TAC[isQaskR] THEN MESON_TAC[]);;

let EHS0 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz.
     valid_quiz Gc rc x0c qz
     ==> MAP (embedqz Gm Gc x0m x0c qz) (walkqz qz Gc x0c) = walkqz qz Gm x0m`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_MAP; SIZE_WALKQZ] THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`x0m:B`; `walkqz qz (Gm:(B)hypermap) x0m`; `i:num`]
    NTHD_EL) THEN
  MP_TAC(ISPECL [`x0c:A`; `walkqz qz (Gc:(A)hypermap) x0c`; `i:num`]
    NTHD_EL) THEN
  ASM_SIMP_TAC[EL_MAP; SIZE_WALKQZ] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_MESON_TAC[DHS0]);;

let ALL_KERNEL_WALKQZ = prove
 (`!(Gc:(A)hypermap) rc x0c qz.
     valid_quiz Gc rc x0c qz ==> ALL (kernel Gc rc) (walkqz qz Gc x0c)`,
  REWRITE_TAC[valid_quiz; GSYM ALL_MEM] THEN MESON_TAC[FBAND_MEM]);;

let EMBEDQZ_CENTRAL = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz.
     valid_quiz Gc rc x0c qz /\ fitqz Gm x0m qz /\ plain_cubic Gm /\
     plain_quasicubic Gc rc /\ x0c IN dart Gc /\ x0m IN dart Gm
     ==> ALL (edge_central Gc Gm (embedqz Gm Gc x0m x0c qz))
             (walkqz qz Gc x0c)`,
  REWRITE_TAC[plain_cubic; plain_quasicubic] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`;
                                      `x0m:B`; `x0c:A`; `rc:(A)list`;
                                      `qz:quiz`] th))
            [EMBEDQZ_FACE; EHS0; DHX0; DHEX0] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x0c:A`; `qz:quiz`]
                ALL_KERNEL_WALKQZ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISQUIZR_STRUCT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `h = embedqz (Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c
                          (Quiz (QaskR qa0 q01) (QaskR qa1 q10))` THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`]
                HC_WALK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[walkqz; walkq; qstepR; MAP; MAP_APPEND; APPEND;
                              CONS_11; ALL; ALL_APPEND; WALKQ_APPEND_EQ]) THEN
  REWRITE_TAC[walkqz; walkq; qstepR; ALL; ALL_APPEND] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[edge_central] THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_SIMP_TAC[CFT_PLAIN_EE]);;

(* ------------------------------------------------------------------------- *)
(* Coq embedqz_rlinked: the edge-central kernel darts are rlink-connected.   *)
(* The band of a dart list grows along the quiz walks (CCRWALK) one dart at  *)
(* a time (RLINK_CONNECTED_SNOC), starting from [x0c; edge x0c].             *)
(* ------------------------------------------------------------------------- *)

let KERNEL_FBAND_ALL = prove
 (`!(Gc:(A)hypermap) rc a x.
     ALL (kernel Gc rc) a /\ fband Gc a x ==> kernel Gc rc x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[FBAND_MEM_IFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[kernel] THEN
  ASM_MESON_TAC[CFT_DART; CFACE_SYM_GEN; FBAND_CFACE]);;

let RLINK_SINGLETON = prove
 (`!(Gc:(A)hypermap) (Gm:(B)hypermap) (h:A->B) x0.
     rlink_connected Gc (\z. fband Gc [x0] z /\ edge_central Gc Gm h z)`,
  REWRITE_TAC[rlink_connected; IN; FBAND_SING] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `[y:A]` THEN
  ASM_REWRITE_TAC[list_path; ALL; LAST; NOT_CONS_NIL] THEN CFACE_TAC[]);;

let RLINK_CONNECTED_SNOC = prove
 (`!(Gc:(A)hypermap) (Gm:(B)hypermap) (h:A->B) a y.
     plain_hypermap Gc /\ plain_hypermap Gm /\
     fband Gc a (edge_map Gc y) /\ edge_central Gc Gm h y /\
     rlink_connected Gc (\z. fband Gc a z /\ edge_central Gc Gm h z)
     ==> rlink_connected Gc
           (\z. fband Gc (APPEND a [y]) z /\ edge_central Gc Gm h z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `edge_central Gc Gm (h:A->B) (edge_map Gc y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_CENTRAL_EDGE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rlink_connected]) THEN
  REWRITE_TAC[rlink_connected; IN; FBAND_APPEND; FBAND_SING; GSYM ALL_MEM]
  THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:A`; `v:A`]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:A`; `edge_map Gc (y:A)`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:(A)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `APPEND p [v:A]` THEN
    ASM_REWRITE_TAC[LIST_PATH_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL;
                    LAST_APPEND; LAST; MEM_APPEND; MEM] THEN
    ASM_SIMP_TAC[LAST; list_path] THEN CONJ_TAC THENL
     [CFACE_TAC[]; ASM_MESON_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`edge_map Gc (y:A)`; `v:A`]) THEN
    ASM_REWRITE_TAC[edgeK] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:(A)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `CONS (y:A) p` THEN
    ASM_REWRITE_TAC[list_path; LAST; NOT_CONS_NIL; MEM] THEN
    ASM_SIMP_TAC[LAST] THEN CONJ_TAC THENL
     [CFACE_TAC[]; ASM_MESON_TAC[CFACE_REFL]];
    EXISTS_TAC `[v:A]` THEN
    ASM_REWRITE_TAC[list_path; LAST; NOT_CONS_NIL; MEM] THEN
    CONJ_TAC THENL [CFACE_TAC[]; ASM_MESON_TAC[]]]);;

(* Coq ccRwalk: growing the band along a walk from node x keeps it           *)
(* rlink-connected.  CCR_TAC closes a goal rlink_connected (fband (APPEND a  *)
(* s) /\ hc) by the induction hypothesis (s a walk) or RLINK_CONNECTED_SNOC  *)
(* (s a singleton) and simplifies the side conditions, recursively.          *)

let rec CCR_TAC g =
 ((FIRST_ASSUM MATCH_MP_TAC ORELSE MATCH_MP_TAC RLINK_CONNECTED_SNOC) THEN
  REPEAT CONJ_TAC THEN
  ((ASM_SIMP_TAC[FBAND_APPEND; FBAND_CONS; FBAND_NIL; FBAND_EN_EQ;
                 FBAND_FACE_MAP_EQ; CFACE_EN_EQ; CFT_PLAIN_EE; CFACE_REFL;
                 ALL_APPEND; ALL; RLINK_SINGLETON] THEN NO_TAC) ORELSE
   CCR_TAC)) g;;

let CCRWALK = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc (h:A->B).
     plain_hypermap Gc /\ quasicubic Gc (set_of_list rc) /\ plain_hypermap Gm
     ==> !q a x.
           fband Gc a x /\ fband Gc a (edge_map Gc x) /\
           ALL (kernel Gc rc) a /\
           rlink_connected Gc (\y. fband Gc a y /\ edge_central Gc Gm h y) /\
           ALL (kernel Gc rc) (walkq q Gc (node_map Gc x)) /\
           ALL (edge_central Gc Gm h) (walkq q Gc (node_map Gc x))
           ==> rlink_connected Gc
                 (\y. fband Gc (APPEND a (walkq q Gc (node_map Gc x))) y /\
                      edge_central Gc Gm h y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] KERNEL_NN_EN_NN) THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] KERNEL_NN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC question_INDUCT THEN
  REWRITE_TAC[walkq; qstepL; qstepR; ALL; ALL_APPEND; APPEND_NIL] THEN
  REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  (SUBGOAL_THEN `kernel Gc rc (x:A) /\ kernel Gc rc (edge_map Gc x)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC KERNEL_FBAND_ALL THEN
     EXISTS_TAC `a:(A)list` THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  ONCE_REWRITE_TAC[APPEND_CONS_SNOC] THEN
  REWRITE_TAC[APPEND_ASSOC; APPEND_NIL] THEN CCR_TAC);;

let FBAND_SPLIT_RING = prove
 (`!(H:(A)hypermap) x y l1 l2 z.
     fband H (APPEND (CONS x l1) (CONS y l2)) z <=>
     fband H (APPEND (APPEND (APPEND [x] [y]) l1) l2) z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FBAND_APPEND; FBAND_CONS; FBAND_NIL] THEN
  CONV_TAC TAUT);;

let EMBEDQZ_RLINKED = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz.
     valid_quiz Gc rc x0c qz /\ fitqz Gm x0m qz /\ plain_cubic Gm /\
     plain_quasicubic Gc rc /\ x0c IN dart Gc /\ x0m IN dart Gm
     ==> rlink_connected Gc
           (\z. kernel Gc rc z /\
                edge_central Gc Gm (embedqz Gm Gc x0m x0c qz) z)`,
  REWRITE_TAC[plain_cubic; plain_quasicubic] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. kernel Gc rc z /\
         edge_central Gc Gm (embedqz (Gm:(B)hypermap) (Gc:(A)hypermap)
                                     x0m x0c qz) z) =
    (\z. fband Gc (walkqz qz Gc x0c) z /\
         edge_central Gc Gm (embedqz Gm Gc x0m x0c qz) z)`
  SUBST1_TAC THENL
   [MP_TAC(ASSUME `valid_quiz (Gc:(A)hypermap) rc x0c qz`) THEN
    REWRITE_TAC[valid_quiz; FUN_EQ_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `x0m:B`; `x0c:A`;
                 `rc:(A)list`; `qz:quiz`] EMBEDQZ_CENTRAL) THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x0c:A`; `qz:quiz`]
                ALL_KERNEL_WALKQZ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISQUIZR_STRUCT) THEN
  ASM_REWRITE_TAC[plain_cubic; plain_quasicubic] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `h = embedqz (Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c
                          (Quiz (QaskR qa0 q01) (QaskR qa1 q10))` THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`]
                CCRWALK) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[walkqz; walkq; qstepR; ALL; ALL_APPEND; FBAND_SPLIT_RING] THEN
  REPEAT STRIP_TAC THEN CCR_TAC);;

(* The quiz pre-embedding theorem (Coq quiz_preembedding).                   *)

let KERNEL_CFACE_WALKQZ = prove
 (`!(Gc:(A)hypermap) rc x0c qz x.
     valid_quiz Gc rc x0c qz /\ kernel Gc rc x
     ==> ?y. MEM y (walkqz qz Gc x0c) /\ cface Gc x y`,
  REWRITE_TAC[valid_quiz; FBAND_MEM_IFF] THEN MESON_TAC[]);;

let QUIZ_PREEMBEDDING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) x0m x0c rc qz.
     valid_quiz Gc rc x0c qz /\ fitqz Gm x0m qz /\ plain_cubic Gm /\
     plain_quasicubic Gc rc /\ x0c IN dart Gc /\ x0m IN dart Gm
     ==> preembedding Gc Gm (embedqz Gm Gc x0m x0c qz) (kernel Gc rc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`;
                                      `x0m:B`; `x0c:A`; `rc:(A)list`;
                                      `qz:quiz`] th))
            [EMBEDQZ_FACE; EMBEDQZ_ARITY; EMBEDQZ_CENTRAL; EMBEDQZ_RLINKED]
  THEN ASM_REWRITE_TAC[preembedding; IN] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x0c:A`; `qz:quiz`; `x:A`]
                KERNEL_CFACE_WALKQZ) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[ALL_MEM_D]);;
