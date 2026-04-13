(*==============================================================================

Monadic Separation Logic (MSL): a monadic reformulation of a class of separation
-logic predicates of functional nature as heap-dependent computations. This
fragment has the benifit of efficient dynamic checking and deterministic search
in entailment proofs. This fragment is shown to be interesting enough to write
commonly seen separation-logic specifications, e.g., recursive representation
predicates for linked data structures.

Traditional separation-logic assertions are defined by an arbitrary set of
subheaps that satisfy the assertion:
    
  SL ≔ (RES)set     [(A)set is a shorthand for A → bool] .

We can define a restriction operation to get the subheaps of a given (full)
heap that satisfy the assertion:
  
  RESTRICT : SL → RES → (RES)set
  RESTRICT P h = {h' | h' ≼ h ∧ P h'}
               = {h' | h' ≼ h} ∩ P        [≼ is the substate relation] .

This restriction operation tells us, given a full heap, which parts of it could
potentially be the occupied substate (known as footprint). A precise separation
-logic assertion is one that for any given heap, there is at most one subheap
that satisfies it:

  IS_PRECISE : SL → bool
  IS_PRECISE P ⇔ ∀h. |RESTRICT P h| ≤ 1
               ⇔ ∀h h1 h2. h1 ≼ h ∧ h2 ≼ h ∧ P h1 ∧ P h2 ⇒ h1 = h2 .

This means the footprint of a precise separation-logic assertion is unique. For
example, the predicate ∃v. x ↦ v is precise, and its footprint is {x ↦ v0} when
x is in the domain of given full heap and v0 is the value at x.

We are especially interested in a class of precise separation-logic assertions
that are "functional". We say a separation-logic predicate (i.e., functions that
return a SL assertion) is functional if some of its arguments can be viewed as
outputs: given a full heap, the footprint subheap and the outputs are uniquely
determined. For example, x ↦ _ is a functional predicate where the address is
given as the input and the value is the output; on the other hand, _ ↦ v is not
a functional predicate because there might be multiple v storing at different
addresses.

More precisely, a functional separation-logic predicate should satisfy
uniqueness properties on footprint and output (assuming inputs are fixed). For
a separation-logic predicate P : OUT → SL:

  (1) IS_PRECISE (∃b:OUT. P b)       [∃ here is lifted into SL]
   ⇔ IS_PRECISE (⋃{P b | b:OUT})
  (2) ∀(b1 b2:OUT) (h:RES). P b1 h ∧ P b2 h ⇒ b1 = b2 .

It is direct that (1) ensures the footprint is unique. Under (1), (2) ensures
the output is also unique. It is not hard to see that (1) ∧ (2) are equivalent
to the following:
  
  (3) IS_FUNCTIONAL P ⇔ ∀h b1 b2 ft1 ft2.
        ft1 ≼ h ∧ ft2 ≼ h ∧ P b1 ft1 ∧ P b2 ft2
        ⇒ b1 = b2 ∧ ft1 = ft2 .

Note that any precise separation-logic assertion can be trivially viewed as a
functional separation-logic predicate by taking the OUT type as unit.

Finally, a functional separation-logic predicate P can be equivalently viewed as
a heap-dependent computation that runs on a heap and returns an output and the
remainder subheap with footprint carved out. This TO_MSL conversion operation
can be specified as:

  (A)MSL ≔ RES → (A × RES) option
  
  TO_MSL : (OUT → SL) → (OUT)MSL
  TO_MSL P = λh. 
    if ∃b ft. P b ft ∧ ft ≼ h then
      SOME (@(b, rm). ∃ft. P b ft ∧ ft ≼ h ∧ rm = REMOVE h ft)
    else NONE
  [@ is the Hilbert choice operator] .

Conversely, the FROM_MSL conversion operation can be specified as:

  FROM_MSL : (OUT)MSL → (OUT → SL)
  FROM_MSL f ⇔ λb h. f h = SOME (b, UNIT)  [UNIT is the empty subheap]

We can prove the following equivalence between the computational view and the
separation-logic predicate view:

  IS_FUNCTIONAL P ⇒ IS_VALID_MSL (TO_MSL P)
  IS_VALID_MSL f ⇒ IS_FUNCTIONAL (FROM_MSL f)
  
  IS_VALID_MSL : (OUT)MSL → bool
  IS_VALID_MSL f ⇔
    (∀h b rm. f h = SOME (b, rm) ⇒ rm ≼ h)           [substate]
    (∀h b rm. f h = SOME (b, rm) ⇒
       ∀frm. h#frm ⇒ f (h⊎frm) = SOME (b, rm⊎frm))   [preservation]
       
    [# is the separation operator, ⊎ is the disjoint union operator] .

But more importantly, many functional separation-logic predicates can be defined
directly as a monadic computation. For example, the predicate _ ↦ _ can be
redefined as:

  data_at : addr → (val)MSL  [assume RES ≔ addr → val]
  data_at x h =
    if x ∈ dom h then
      SOME (h x, h\{x})  [\ is the set difference operator]
    else NONE

Well-behaved MSL computations form a monad. The bind operation composes MSL
computations by passing on the remainder heap of the first computation and
the output of the first computation as inputs to the next computation:

  RET : OUT → (OUT)MSL
  RET x = SOME (x, UNIT)

  BIND : (A)MSL → (A → (B)MSL) → (B)MSL
  BIND f g h =
    match f h with
    | NONE -> NONE
    | SOME (b, rm) -> f b (REMOVE h rm)

Apart from these basic monadic operations, we can define some other useful
operations that also preserve well-behavedness. For example, using these
operations and the computational view of data_at, the traditioanl singly-linked
list predicate

  sll_at : (addr: val) -> (values: val list) -> SL
  sll p l =
    match l with
    | [] -> ⎡p = null⎤
    | hd :: tl ->
      ∃hd nxt. ⎡p ≠ null⎤ ⋆ p ↦ (hd,nxt) ⋆ sll nxt tl

can be rewritten as a monadic computation:

  sll_at : addr → (val list)MSL
  sll_at p =
    if l = [] then
      RET []
    else
      BIND (data_at p) (λhd.
      BIND (data_at (p + 1)) (λnxt.
      BIND (sll_at nxt) (λtl.
      RET (hd :: tl))))


==============================================================================*)

(*------------------------------------------------------------------------------
  We model undefinedness in partial operations as NONE.
------------------------------------------------------------------------------*)
let IS_SOME_DEF = new_definition `!x : (A)option. IS_SOME x = ?y. x = SOME y`;;
let IS_SOME_SOME = prove(`!x : A. IS_SOME (SOME x)`, METIS_TAC [IS_SOME_DEF]);;
let IS_SOME_NONE = prove(`~IS_SOME NONE`, REWRITE_TAC [IS_SOME_DEF; option_DISTINCT]);;

(*------------------------------------------------------------------------------
  Resource algebra: PCM + cancellative + well-foundedness. It is
  used to model resources that can be separately owned and exhausted.
------------------------------------------------------------------------------*)
new_type ("RES", 0);;
new_constant("UNIT", `:RES`);;
new_constant ("JOIN", `:RES option->RES option->RES option`);;

let JOIN_UNDEF_RIGHT = new_axiom `!x. JOIN x NONE = NONE`;;
let JOIN_ASSOC = new_axiom `!x y z. JOIN (JOIN x y) z = JOIN x (JOIN y z)`;;
let JOIN_COMM = new_axiom `!x y. JOIN x y = JOIN y x`;;
let JOIN_UNIT_RIGHT = new_axiom `!x. JOIN x (SOME UNIT) = x`;;

let JOIN_UNDEF_LEFT = prove(`!x. JOIN NONE x = NONE`,
  REWRITE_TAC [JOIN_COMM; JOIN_UNDEF_RIGHT]);;
let JOIN_UNIT_LEFT = prove(`!x. JOIN (SOME UNIT) x = x`,
  REWRITE_TAC [JOIN_COMM; JOIN_UNIT_RIGHT]);;

let JOIN_UNIT_UNIQUE = prove(`?!u. !x. JOIN x (SOME u) = x`,
  REWRITE_TAC [EXISTS_UNIQUE] THEN
  EXISTS_TAC `UNIT` THEN
  CONJ_TAC THENL [
    ACCEPT_TAC JOIN_UNIT_RIGHT;
    FIX_TAC "[u]" THEN
    DISCH_THEN (fun th -> ASSUME_TAC (SPEC `SOME UNIT` th)) THEN
    ASM_MESON_TAC [option_INJ; JOIN_UNIT_LEFT]
  ]
);;

let JOIN_SOME_IMP = prove(
  `!x y z. (JOIN x y = SOME z) ==> ?a b. x = SOME a /\ y = SOME b`,
  FIX_TAC "x y z" THEN
  STRUCT_CASES_THEN (fun eq -> SUBST1_TAC eq) (ISPEC `x:RES option` (cases "option")) THEN
  STRUCT_CASES_THEN (fun eq -> SUBST1_TAC eq) (ISPEC `y:RES option` (cases "option")) THEN
  MESON_TAC [JOIN_UNDEF_LEFT; JOIN_UNDEF_RIGHT; option_DISTINCT]
);;

let IS_SEP_DEF = new_definition
  `!x:RES y:RES. IS_SEP x y = ?z. JOIN (SOME x) (SOME y) = SOME z`;;
let IS_SUB_DEF = new_definition
  `!x:RES y:RES. IS_SUB x y = ?z. JOIN (SOME x) (SOME z) = SOME y`;;
let REMOVE_DEF = new_definition
  `!x:RES y:RES. REMOVE x y = @z. JOIN (SOME y) (SOME z) = SOME x`;;

let REMOVE_THM = prove(
  `!x y. IS_SUB y x ==> JOIN (SOME y) (SOME (REMOVE x y)) = SOME x`,
  MESON_TAC [IS_SUB_DEF; REMOVE_DEF]
);;

let IS_SUB_UNIT = prove(`!x. IS_SUB UNIT x`, MESON_TAC [IS_SUB_DEF; JOIN_UNIT_LEFT]);;

let IS_SUB_REFL = prove(`!x. IS_SUB x x`, MESON_TAC [IS_SUB_DEF; JOIN_UNIT_RIGHT]);;

let IS_SUB_TRANS = prove(`!x y z. IS_SUB x y /\ IS_SUB y z ==> IS_SUB x z`,
  REWRITE_TAC [IS_SUB_DEF] THEN
  INTRO_TAC "![a/x] [ab/y] [abc/z]; (@b. Jab) (@c. Jabc)" THEN
  REMOVE_THEN "Jab" (fun ab ->
    REMOVE_THEN "Jabc" (fun abc ->
      LABEL_TAC "Jabc" (PURE_REWRITE_RULE [GSYM ab; JOIN_ASSOC] abc))) THEN
  USE_THEN "Jabc" (MP_TAC o MATCH_MP JOIN_SOME_IMP) THEN
  INTRO_TAC "@a' bc. _ Jbc" THEN
  EXISTS_TAC `bc:RES` THEN ASM_MESON_TAC []
);;
(* MESON_TAC [IS_SUB_DEF; JOIN_ASSOC; JOIN_SOME_IMP]) *)

let JOIN_CANCEL_LEFT = new_axiom
  `!x y z. JOIN x y = JOIN x z /\ IS_SOME (JOIN x y) ==> y = z`;;
let JOIN_CANCEL_RIGHT = prove(
  `!x y z. JOIN y x = JOIN z x /\ IS_SOME (JOIN y x) ==> y = z`,
  REWRITE_TAC [JOIN_COMM; JOIN_CANCEL_LEFT]);;

let JOIN_UNIT_UNIT = prove(`?!u. JOIN (SOME u) (SOME u) = SOME u`,
  REWRITE_TAC [EXISTS_UNIQUE] THEN
  EXISTS_TAC `UNIT` THEN
  CONJ_TAC THENL [
    MATCH_ACCEPT_TAC JOIN_UNIT_RIGHT;
    FIX_TAC "[u]" THEN
    MP_TAC (ISPEC `SOME (u:RES)` JOIN_UNIT_LEFT) THEN
    MESON_TAC [JOIN_CANCEL_RIGHT; option_INJ; IS_SOME_SOME]
  ]
);;

let JOIN_SELF_IMP = prove(`!x y. JOIN (SOME x) y = SOME x ==> y = SOME UNIT`,
  FIX_TAC "x y" THEN
  MP_TAC (ISPEC `SOME (x:RES)` JOIN_UNIT_RIGHT) THEN
  MESON_TAC [JOIN_CANCEL_LEFT; IS_SOME_SOME]
);;

let SUB_PROPER_DEF = new_definition `!x y. SUB_PROPER x y <=> IS_SUB x y /\ ~(x = y)`;;
let SUB_PROPER_WF = new_axiom `WF (SUB_PROPER)`;;

let JOIN_POSITIVE = prove(
  `!x y. JOIN (SOME x) (SOME y) = SOME UNIT ==> x = UNIT /\ y = UNIT`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (* Step 1: IS_SUB x UNIT and IS_SUB UNIT x *)
  SUBGOAL_THEN `IS_SUB x UNIT` ASSUME_TAC THENL [
    REWRITE_TAC [IS_SUB_DEF] THEN ASM_MESON_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `IS_SUB UNIT x` ASSUME_TAC THENL [
    ACCEPT_TAC (SPEC `x:RES` IS_SUB_UNIT); ALL_TAC] THEN
  (* Step 2: x = UNIT by contradiction using WF_ANTISYM *)
  SUBGOAL_THEN `x:RES = UNIT` ASSUME_TAC THENL [
    ASM_CASES_TAC `x:RES = UNIT` THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (MP (ISPECL [`SUB_PROPER`; `x:RES`; `UNIT:RES`] WF_ANTISYM) SUB_PROPER_WF) THEN
    REWRITE_TAC [SUB_PROPER_DEF] THEN
    ASM_MESON_TAC [];
    ALL_TAC] THEN
  (* Step 3: y = UNIT from x = UNIT *)
  ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN `JOIN (SOME UNIT) (SOME y) = SOME UNIT` MP_TAC THENL [
    ASM_MESON_TAC [];
    REWRITE_TAC [JOIN_UNIT_LEFT] THEN MESON_TAC [option_INJ]]
);;

let IS_SUB_ANTISYM = prove(`!x y. IS_SUB x y /\ IS_SUB y x ==> x = y`,
  REWRITE_TAC [IS_SUB_DEF] THEN
  INTRO_TAC "!x y; (@a. Jxa) (@b. Jyb)" THEN
  USE_THEN "Jxa" (fun xa ->
    REMOVE_THEN "Jyb" (fun yb ->
      LABEL_TAC "Jxab" (PURE_REWRITE_RULE [GSYM xa; JOIN_ASSOC] yb))) THEN
  REMOVE_THEN "Jxab" (fun xab ->
    MP_TAC (MATCH_MP JOIN_SELF_IMP xab)
  ) THEN
  DISCH_THEN (fun th -> STRIP_ASSUME_TAC (MATCH_MP JOIN_POSITIVE th)) THEN
  ASM_MESON_TAC [option_INJ; JOIN_UNIT_RIGHT]
);;


(*---------------------------------------------------------------------------
  Traditional precise separation logic predicates.
---------------------------------------------------------------------------*)

let SL_IND, SL_REC = define_type "SL = SLProp (RES -> bool)";;
let IS_PRECISE_DEF = define `!p:RES->bool. IS_PRECISE (SLProp p) <=>
  !x y1 y2. IS_SUB y1 x /\ IS_SUB y2 x /\ p y1 /\ p y2 ==> y1 = y2`;;


(* ========================================================================= *)
(* Computational precise separation logic (footprint-based semantics).       *)
(*                                                                           *)
(* RUN p r = SOME (ft, a) means:                                             *)
(*   p succeeds on resource r, its footprint is ft (<= r), returning a.      *)
(*   The remainder (unconsumed resource) is implicitly REMOVE r ft.          *)
(* ========================================================================= *)

let CSL_IND, CSL_REC = define_type "CSL = CSLProp (RES -> (RES # A)option)";;
let RUN_DEF = define `RUN (CSLProp p) = p`;;


(* Validity conditions:
   1. footprint validity: ft <= r, and ft is self-sufficient (tightness);
   2. determinism under extension: enlarging the input does not change the result *)
let VALID_DEF = define `VALID (CSLProp p: (A)CSL) <=>
  (!r ft a. p r = SOME (ft, a) ==> IS_SUB ft r /\ p ft = SOME (ft, a)) /\
  (!r1 r2. IS_SOME (p r1) /\ IS_SUB r1 r2 ==> p r2 = p r1)
`;;

(* ------------------------------------------------------------------------- *)
(* Erasure and lifting: bridge between CSL and classical precise SL.         *)
(* ------------------------------------------------------------------------- *)

(* Erase computational content: r satisfies the predicate iff r is a footprint
   (i.e., a fixed point: running on r returns r itself). *)
let ERASE_DEF = define `ERASE (CSLProp p: (A)CSL) =
  SLProp (\r:RES. ?a:A. p r = SOME (r, a))`;;

(* Lift a precise predicate: find the unique substate satisfying q, return it
   as the footprint. *)
let LIFT_DEF = define `LIFT (SLProp q:SL) : (1)CSL =
  CSLProp (\r:RES.
    if (?ft. IS_SUB ft r /\ q ft)
    then SOME ((@ft. IS_SUB ft r /\ q ft), one)
    else NONE)`;;

(* ========================================================================= *)
(* Combinators (footprint-based)                                           *)
(* ========================================================================= *)

let FAIL_DEF = new_definition `FAIL : (A)CSL = CSLProp (\r:RES. NONE)`;;

(* RET: consumes nothing, footprint = UNIT *)
let RET_DEF = new_definition `RET (x:A) : (A)CSL = CSLProp (\r:RES. SOME (UNIT, x))`;;

let EMP_DEF = new_definition `EMP : (1)CSL = RET one`;;
let PROP_DEF = new_definition `PROP (p:bool) : (1)CSL = if p then EMP else FAIL`;;

(* BIND: run p on r to get footprint ft_p, then run (f a) on the remainder
   REMOVE r ft_p, and combine the two footprints via JOIN. *)
let BIND_DEF = new_definition `BIND (p:(A)CSL) (f:A->(B)CSL) : (B)CSL =
  CSLProp (\r:RES.
    match RUN p r with
    | NONE -> NONE
    | SOME (ft_p, a) ->
      match RUN (f a) (REMOVE r ft_p) with
      | NONE -> NONE
      | SOME (ft_f, b) ->
        match JOIN (SOME ft_p) (SOME ft_f) with
        | NONE -> NONE
        | SOME ft -> SOME (ft, b))`;;

let SEQ_DEF = new_definition `SEQ (p:(A)CSL) (q:(B)CSL) : (B)CSL = BIND p (\(_:A). q)`;;
let MAP_DEF = new_definition `MAP (f:A->B) (p:(A)CSL) : (B)CSL = BIND p (\a. RET (f a))`;;
let STAR_DEF = new_definition `STAR (p:(A)CSL) (q:(B)CSL) : (A#B)CSL =
  BIND p (\a. MAP (\b. (a,b)) q)`;;

(* EXISTS: requires a coherence side-condition *)
let EXISTS_DEF = new_definition `EXISTS (f:A->(B)CSL) : (B)CSL =
  CSLProp (\r:RES.
    if ?a. IS_SOME (RUN (f a) r)
    then RUN (f (@a. IS_SOME (RUN (f a) r))) r
    else NONE)`;;

(* ========================================================================= *)
(* Characterization theorems: VALID <-> IS_PRECISE via ERASE / LIFT          *)
(* ========================================================================= *)

(* Thm 1: VALID p ==> IS_PRECISE (ERASE p)
   Proof: by monotonicity, any two fixed-point substates of x
   produce the same result on x, hence are equal. *)

(* Thm 2: IS_PRECISE (SLProp q) ==> VALID (LIFT (SLProp q))
   Proof: tightness by IS_SUB_REFL + precision;
   monotonicity by IS_SUB_TRANS + precision. *)

(* Thm 3 (round-trip):
   IS_PRECISE (SLProp q) ==> ERASE (LIFT (SLProp q)) = SLProp q
   VALID p ==> LIFT (ERASE p) = p    (when A = 1) *)

(* Thm 4 (main characterization):
   IS_PRECISE (SLProp q) <=> ?p:(1)CSL. VALID p /\ ERASE p = SLProp q *)

(* ========================================================================= *)
(* Validity Proofs                                                           *)
(* ========================================================================= *)

(* TODO: rewrite validity proofs for footprint-passing combinators.
   Key structure for BIND_VALID:
     VALID p /\ VALID (f a) ==>
     - tightness: ft_p is a fixed point of p, ft_f of (f a);
       REMOVE ft ft_p = ft_f (since ft is JOIN of ft_p and ft_f);
       run (f a) on ft_f returns (ft_f, b), so BIND on ft returns (ft, b).
     - monotonicity: p returns same ft_p on any r' >= r (by p's monotonicity);
       REMOVE r' ft_p >= REMOVE r ft_p, so (f a) returns same ft_f
       (by (f a)'s monotonicity); JOIN ft_p ft_f is unchanged. *)

(* TODO: EXISTS_VALID needs a coherence condition:
     !a b r. IS_SOME(RUN (f a) r) /\ IS_SOME(RUN (f b) r)
       ==> RUN (f a) r = RUN (f b) r
   Without this, epsilon-chosen witness may change after extension. *)
