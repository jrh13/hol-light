(* ========================================================================= *)
(* Abstract version of symbolic trajectory evaluation.                       *)
(*                                                                           *)
(* Based on the paper "Symbolic Trajectory Evaluation in a Nutshell"         *)
(* by Tom Melham & Ashish Darbari, 2002 (still unpublished?)                 *)
(* ========================================================================= *)

parse_as_infix("&&",(16,"right"));;
parse_as_infix("<<=",(14,"right"));;
parse_as_infix(">->",(13,"right"));;
parse_as_infix(">~~>",(6,"right"));;

(* ------------------------------------------------------------------------- *)
(* Some type of nodes that we don't really care much about.                  *)
(* ------------------------------------------------------------------------- *)

let node_INDUCT,node_RECURSION = define_type
  "node = Node num";;

(* ------------------------------------------------------------------------- *)
(* Also "abstract" propositional formulas (i.e. we never unfold "eval").     *)
(* ------------------------------------------------------------------------- *)

let propform_INDUCT,propform_RECURSION = define_type
  "propform = Propform (num->bool)->bool";;

let eval = new_recursive_definition propform_RECURSION
  `eval (Propform p) v = p v`;;

(* ------------------------------------------------------------------------- *)
(* Quaternary lattice.                                                       *)
(* ------------------------------------------------------------------------- *)

let quat_INDUCT,quat_RECURSION = define_type
 "quat = X | ZERO | ONE | TOP";;

let quat_DISTINCT = prove_constructors_distinct quat_RECURSION;;

(* ------------------------------------------------------------------------- *)
(* Basic lattice operations.                                                 *)
(* ------------------------------------------------------------------------- *)

let qle = new_definition
  `x <<= y <=> x = X \/ y = TOP \/ x = y`;;

let qjoin = new_definition
  `x && y = if x <<= y then y else if y <<= x then x else TOP`;;

(* ------------------------------------------------------------------------- *)
(* Trivial lemmas about the quaternary lattice.                              *)
(* ------------------------------------------------------------------------- *)

let QLE_REFL = prove
 (`!x. x <<= x`,
  REWRITE_TAC[qle]);;

let QLE_TRANS = prove
 (`!x y z. x <<= y /\ y <<= z ==> x <<= z`,
  REPEAT(MATCH_MP_TAC quat_INDUCT THEN REPEAT CONJ_TAC) THEN
  REWRITE_TAC[qle; quat_DISTINCT]);;

let QLE_LJOIN = prove
 (`!x y z. x && y <<= z <=> x <<= z /\ y <<= z`,
  REPEAT(MATCH_MP_TAC quat_INDUCT THEN REPEAT CONJ_TAC) THEN
  REWRITE_TAC[qjoin; qle; quat_DISTINCT]);;

let QLE_RJOIN = prove
 (`!x y. x <<= x && y /\ y <<= x && y`,
  REPEAT(MATCH_MP_TAC quat_INDUCT THEN REPEAT CONJ_TAC) THEN
  REWRITE_TAC[qjoin; qle; quat_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* Choice expressions.                                                       *)
(* ------------------------------------------------------------------------- *)

let choice = new_definition
  `b >-> x = if b then x else X`;;

let QLE_CHOICE = prove
 (`(b >-> x) <<= y <=> b ==> x <<= y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[choice] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN REWRITE_TAC[qle]);;

(* ------------------------------------------------------------------------- *)
(* Basic type of trajectory formulas.                                        *)
(* ------------------------------------------------------------------------- *)

let trajform_INDUCT,trajform_RECURSION = define_type
 "trajform = Is_0 node
           | Is_1 node
           | Andj trajform trajform
           | When trajform propform
           | Next trajform";;

(* ------------------------------------------------------------------------- *)
(* Semantics.                                                                *)
(* ------------------------------------------------------------------------- *)

let tholds = new_recursive_definition trajform_RECURSION
  `(tholds (Is_0 nd) seq v <=> ZERO <<= seq 0 nd v) /\
   (tholds (Is_1 nd) seq v <=> ONE <<= seq 0 nd v) /\
   (tholds (Andj tf1 tf2) seq v <=> tholds tf1 seq v /\ tholds tf2 seq v) /\
   (tholds (When tf1 p) seq v <=> eval p v ==> tholds tf1 seq v) /\
   (tholds (Next(tf1)) seq v <=> tholds tf1 (\t. seq(t + 1)) v)`;;

(* ------------------------------------------------------------------------- *)
(* Defining sequence.                                                        *)
(* ------------------------------------------------------------------------- *)

let defseq = new_recursive_definition trajform_RECURSION
  `(defseq (Is_0 n) t nd v = ((n = nd) /\ (t = 0)) >-> ZERO) /\
   (defseq (Is_1 n) t nd v = ((n = nd) /\ (t = 0)) >-> ONE) /\
   (defseq (Andj tf1 tf2) t nd v = defseq tf1 t nd v && defseq tf2 t nd v) /\
   (defseq (When tf1 p) t nd v =  eval p v >-> defseq tf1 t nd v) /\
   (defseq (Next(tf1)) t nd v = ~(t = 0) >-> defseq tf1 (t - 1) nd v)`;;

(* ------------------------------------------------------------------------- *)
(* Proof of the key property.                                                *)
(* ------------------------------------------------------------------------- *)

let DEFSEQ_MINIMAL = prove
 (`!tf seq v. tholds tf seq v <=> !t nd. defseq tf t nd v <<= seq t nd v`,
  let cases_lemma = prove
   (`(!t. P t) <=> P 0 /\ !t. P(SUC t)`,MESON_TAC[num_CASES]) in
  MATCH_MP_TAC trajform_INDUCT THEN REWRITE_TAC[defseq; tholds] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[QLE_CHOICE] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[QLE_CHOICE] THEN MESON_TAC[];
    SIMP_TAC[QLE_LJOIN; FORALL_AND_THM];
    REWRITE_TAC[QLE_CHOICE] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[cases_lemma] THEN
    ASM_REWRITE_TAC[QLE_CHOICE; NOT_SUC; ADD1; ADD_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* Notion of a trajectory w.r.t. a next-state function.                      *)
(* ------------------------------------------------------------------------- *)

let trajectory = new_definition
  `trajectory next seq v <=> !t nd. next(seq t) nd v <<= seq (t + 1) nd v`;;

(* ------------------------------------------------------------------------- *)
(* Defining trajectory of a formula.                                         *)
(* ------------------------------------------------------------------------- *)

let deftraj = new_recursive_definition num_RECURSION
  `(deftraj step tf 0 nd v = defseq tf 0 nd v) /\
   (deftraj step tf (SUC t) nd v =
        defseq tf (SUC t) nd v && step(deftraj step tf t) nd v)`;;

(* ------------------------------------------------------------------------- *)
(* Obviously this is at least as strong as the defining sequence.            *)
(* ------------------------------------------------------------------------- *)

let DEFTRAJ_DEFSEQ = prove
 (`!tf t nd v. defseq tf t nd v <<= deftraj step tf t nd v`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[deftraj; QLE_REFL; QLE_RJOIN]);;

(* ------------------------------------------------------------------------- *)
(* ...and it is indeed a trajectory.                                         *)
(* ------------------------------------------------------------------------- *)

let TRAJECTORY_DEFTRAJ = prove
 (`!step tf v. trajectory step (deftraj step tf) v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trajectory] THEN
  REWRITE_TAC[GSYM ADD1; deftraj; QLE_RJOIN]);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity of next-state function.                                      *)
(* ------------------------------------------------------------------------- *)

let monotonic = new_definition
 `monotonic next v <=>
   !s1 s2. (!nd. s1 nd v <<= s2 nd v) ==> !nd. next s1 nd v <<= next s2 nd v`;;

(* ------------------------------------------------------------------------- *)
(* Minimality property of defining trajectory (needs monotonicity).          *)
(* ------------------------------------------------------------------------- *)

let DEFTRAJ_MINIMAL = prove
 (`!step v.
      monotonic step v
      ==> !tf seq. trajectory step seq v
                   ==> (tholds tf seq v <=>
                        !t nd. deftraj step tf t nd v <<= seq t nd v)`,
  REWRITE_TAC[monotonic; trajectory; RIGHT_IMP_FORALL_THM] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[DEFSEQ_MINIMAL; DEFTRAJ_DEFSEQ; QLE_TRANS]] THEN
  DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[deftraj; QLE_LJOIN] THEN
  ASM_MESON_TAC[DEFSEQ_MINIMAL; QLE_TRANS; ADD1]);;

(* ------------------------------------------------------------------------- *)
(* Basic semantic notion in STE.                                             *)
(* ------------------------------------------------------------------------- *)

let ste = new_definition
  `(A >~~> C) ckt v <=>
      !seq. trajectory ckt seq v /\ tholds A seq v ==> tholds C seq v`;;

(* ------------------------------------------------------------------------- *)
(* The "fundamental theorem of STE".                                         *)
(* ------------------------------------------------------------------------- *)

let STE_THM = prove
 (`monotonic ckt v
   ==> ((A >~~> C) ckt v <=> !t nd. defseq C t nd v <<= deftraj ckt A t nd v)`,
  MESON_TAC[ste; DEFTRAJ_MINIMAL; DEFSEQ_MINIMAL; DEFTRAJ_DEFSEQ;
            TRAJECTORY_DEFTRAJ; QLE_TRANS]);;
