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
return a SL assertion) is functional if its arguments can be split into inputs
and outputs (i.e., P : IN × OUT → SL for some types IN and OUT), and its inputs
uniquely determine the output as well as the footprint. Intuitively, _ ↦ _ is a
functional predicate where the input is the address and the output is the value.

More precisely, a functional separation-logic predicate P should satisfy two
uniqueness properties on footprint and output for any given input:

  (1) ∀(a:IN). IS_PRECISE (∃b:OUT. P (a, b))       [∃ here is lifted into SL]
   ⇔ ∀(a:IN). IS_PRECISE (⋃{P (a, b) | b:OUT})
  
  (2) ∀(a:IN) (b1 b2:OUT) (h:RES). P (a, b1) h ∧ P (a, b2) h ⇒ b1 = b2 .

It is not hard to see that (1) and (2) are equivalent to the following property:
  
  (3) IS_FUNCTIONAL : (IN × OUT → SL) → bool
  IS_FUNCTIONAL P ⇔ ∀a h b1 b2 h1 h2.
        h1 ≼ h ∧ h2 ≼ h ∧ P (a, b1) h1 ∧ P (a, b2) h2
        ⇒ b1 = b2 ∧ h1 = h2

Note that any precise separation-logic assertion can be trivially viewed as a
functional separation-logic predicate by taking all free variables as input with
the OUT type unit.

Finally, a functional separation-logic predicate P can be equivalently viewed as
a monadic computation that runs on a heap and returns an output as well as the
footprint subheap. This RUN operation could be defined using the Hilbert
operator:

  (A)MSL ≔ RES → (A × RES) option
  
  RUN : (IN × OUT → SL) → (IN → (OUT)MSL)
  RUN P a h = 
    if ∃b ft. P (a, b) ft ∧ ft ≼ h then
      SOME (@(b, ft). P (a, b) ft ∧ ft ≼ h)   [@ is the Hilbert choice operator]
    else NONE

But more importantly, many functional separation-logic predicates can be defined
directly as a monadic computation. For example, the predicate _ ↦ _ can be
redefined as:

  data_at : addr → (val)MSL  [assume RES ≔ addr → val]
  data_at x h =
    if x ∈ dom h then
      SOME (h x, {x ↦ h x})
    else NONE

We can prove the following equivalence between the computational view and the
traditional separation-logic view:

  IS_FUNCTIONAL P ⇔ WELL_BEHAVED (RUN P)
  
  WELL_BEHAVED : (B)MSL → bool
  WELL_BEHAVED f ⇔
    [sufficiency]   (∀h. ∃b ft. f h = SOME (b, ft) ⇒ ft ≼ h ∧ P (a, b) ft) ∧
    [preservation]  (∀h h' b ft. h ≼ h' ∧ f h = SOME (b, ft)
                            ⇒ f h' = SOME (b, ft))

  

The bind operation passes on the result and the remainder heap to the next
computation:

  BIND : (A)MSL → (A → (B)MSL) → (B)MSL
  
  Well-behaved MSL computations correspond to a class of precise-and-functional
  separation-logic predicates.
  
  These programs must be well-behaved: a frame-preserving and a determinism condition is imposed.

  Formally, for any predicate p : (in:A) -> (out:B) -> (h:RES) -> bool, a MSL
  predicate msl(p): A -> RES -> (B # RES) option can be constructed:

  msl(p) = λ (in:A) (h:RES). 
   
  When the following conditions are met on p, msl(p) is well-behaved:
  
    - for all (in:A) (out:B). IS_PRECISE (p in out)
    - for all (h:RES) (in:A) (out1 out2:B).
        p in out1 h /\ p in out2 h ==> out1 = out2

  Expressing specifications in this way is good for dynamic checking and
  deterministic entailment proofs.

  For example, the traditioanl singly-linked list predicate:

  sll : (addr : val) -> (l : val list) -> 

  It can be rewritten as:

  list : addr → (val list)CSL
  list x =
    cond (x = null)
      (return [])
      (bind (read_at x) (λv.
        bind (read_at (x + 1)) (λnext.
          bind (list next) (λrest.
            return (v :: rest)))))


==============================================================================*)

(*------------------------------------------------------------------------------
  We model undefinedness in partial operations as NONE.
------------------------------------------------------------------------------*)
let IS_SOME_DEF = new_definition `!x : (A)option. IS_SOME x = ?y. x = SOME y`;;
let IS_SOME_SOME = prove(`!x : A. IS_SOME (SOME x)`, METIS_TAC [IS_SOME_DEF]);;
let IS_SOME_NONE = prove(`~IS_SOME NONE`, REWRITE_TAC [IS_SOME_DEF; option_DISTINCT]);;

(*------------------------------------------------------------------------------
  Resource algebra: PCM + cancellative + positivity + well-foundedness. It is
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

(* TODO: should follow from SUB_PROPER_WF. Otherwise infinite chain of x < UNIT < x < UNIT < ... *)
let JOIN_POSITIVE = new_axiom
  `!x y. JOIN (SOME x) (SOME y) = SOME UNIT ==> x = UNIT /\ y = UNIT`;;

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
let IS_PRECISE_ALT = prove(`!p:RES->bool. IS_PRECISE (SLProp p) <=>
  !y. p y ==> !x. IS_SUB y x ==> (?!ft. IS_SUB ft x /\ p ft)`,
  MESON_TAC[IS_PRECISE_DEF]
);;


(* ========================================================================= *)
(* Computational precise separation logic (footprint-based semantics).     *)
(*                                                                           *)
(* RUN p r = SOME (ft, a) means:                                             *)
(*   p succeeds on resource r, its footprint is ft (<= r), returning a.     *)
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
