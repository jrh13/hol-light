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

let IS_PRECISE_DEF = define `IS_PRECISE p <=>
  !x y1 y2. IS_SUB y1 x /\ IS_SUB y2 x /\ p y1 /\ p y2 ==> y1 = y2`;;

(* IS_FUNCTIONAL: a functional SL predicate P : A -> RES -> bool has its
   footprint and output uniquely determined by any super-resource h. *)
let IS_FUNCTIONAL_DEF = new_definition
  `IS_FUNCTIONAL (P:A->RES->bool) <=>
   !h b1 b2 ft1 ft2. IS_SUB ft1 h /\ IS_SUB ft2 h /\
                      P b1 ft1 /\ P b2 ft2 ==> b1 = b2 /\ ft1 = ft2`;;

(* Equivalence: IS_FUNCTIONAL P <=> (1) precision of the existential lift
   and (2) output uniqueness on the same footprint. *)
let IS_FUNCTIONAL_ALT = prove(
  `!P:A->RES->bool. IS_FUNCTIONAL P <=>
    IS_PRECISE (\h. ?b. P b h) /\
    (!b1 b2 h. P b1 h /\ P b2 h ==> b1 = b2)`,
  GEN_TAC THEN REWRITE_TAC [IS_FUNCTIONAL_DEF; IS_PRECISE_DEF] THEN
  MESON_TAC [IS_SUB_REFL]);;


(* ========================================================================= *)
(* Monadic Separation Logic (remainder-passing semantics).                   *)
(*                                                                           *)
(* f h = SOME (b, rm) means:                                                 *)
(*   f succeeds on resource h, returning output b with remainder rm.         *)
(*   The footprint (consumed resource) is implicitly REMOVE h rm.            *)
(* ========================================================================= *)

(* Helper: REMOVE inverts JOIN (cancellation via Hilbert choice). *)
let REMOVE_CANCEL = prove(
  `!x y z. JOIN (SOME x) (SOME y) = SOME z ==> REMOVE z x = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IS_SUB x z` ASSUME_TAC THENL [
    REWRITE_TAC [IS_SUB_DEF] THEN ASM_MESON_TAC []; ALL_TAC] THEN
  MP_TAC (SPECL [`z:RES`; `x:RES`] REMOVE_THM) THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`SOME (x:RES)`; `SOME (y:RES)`; `SOME (REMOVE z x)`]
    JOIN_CANCEL_LEFT) THEN
  ASM_REWRITE_TAC [IS_SOME_SOME] THEN
  MESON_TAC [option_INJ]);;

(* Validity conditions for MSL computations (remainder-passing).
   1. Substate: the remainder rm is a substate of the input h.
   2. Frame preservation: adding a compatible frame frm to the input adds the
      same frame to the remainder. *)
let IS_VALID_MSL_DEF = new_definition
  `IS_VALID_MSL (f:RES->(A#RES)option) <=>
   (!h b rm. f h = SOME (b,rm) ==> IS_SUB rm h) /\
   (!h b rm frm h'. f h = SOME (b,rm) /\ JOIN (SOME h) (SOME frm) = SOME h'
     ==> ?rm'. JOIN (SOME rm) (SOME frm) = SOME rm' /\ f h' = SOME (b,rm'))`;;

(* FROM_MSL: extract the SL predicate from an MSL computation.
   A resource h is a footprint of f for output b iff running f on h
   returns b with empty remainder. *)
let FROM_MSL_DEF = new_definition
  `FROM_MSL (f:RES->(A#RES)option) (b:A) (h:RES) <=> f h = SOME (b, UNIT)`;;

(* TO_MSL: convert a functional SL predicate to an MSL computation.
   Given input h, find the unique footprint ft satisfying P, return the
   output and the remainder REMOVE h ft. *)
let TO_MSL_DEF = new_definition
  `TO_MSL (P:A->RES->bool) (h:RES) : (A#RES)option =
   if (?b ft. P b ft /\ IS_SUB ft h) then
     SOME ((@b:A. ?ft. P b ft /\ IS_SUB ft h),
           REMOVE h (@ft:RES. ?b:A. P b ft /\ IS_SUB ft h))
   else NONE`;;


(* ========================================================================= *)
(* Correspondence: IS_VALID_MSL <-> IS_FUNCTIONAL via FROM_MSL / TO_MSL      *)
(* ========================================================================= *)

(* Direction 1: every valid MSL computation induces a functional predicate.
   Proof idea: by frame preservation, f ft_i = SOME (b_i, UNIT) lifts to
   f h = SOME (b_i, rm_i) for the same h; injectivity of f h forces
   b1 = b2 and rm1 = rm2; then JOIN cancellation gives ft1 = ft2. *)
let FROM_MSL_FUNCTIONAL = prove(
  `!f:RES->(A#RES)option. IS_VALID_MSL f ==> IS_FUNCTIONAL (FROM_MSL f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [IS_FUNCTIONAL_DEF; FROM_MSL_DEF] THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [IS_VALID_MSL_DEF]) THEN
  INTRO_TAC "!h b1 b2 ft1 ft2; sub1 sub2 f1 f2" THEN
  (* Decompose IS_SUB into JOIN witnesses *)
  SUBGOAL_THEN `?rm1. JOIN (SOME ft1) (SOME rm1) = SOME h` STRIP_ASSUME_TAC THENL [
    ASM_MESON_TAC [IS_SUB_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `?rm2. JOIN (SOME ft2) (SOME rm2) = SOME h` STRIP_ASSUME_TAC THENL [
    ASM_MESON_TAC [IS_SUB_DEF]; ALL_TAC] THEN
  (* Lift f ft1 = SOME (b1, UNIT) to f h = SOME (b1, rm1) via preservation *)
  SUBGOAL_THEN `(f:RES->(A#RES)option) h = SOME (b1, rm1:RES)` ASSUME_TAC THENL [
    FIRST_X_ASSUM (MP_TAC o SPECL [`ft1:RES`; `b1:A`; `UNIT:RES`; `rm1:RES`; `h:RES`]) THEN
    ASM_REWRITE_TAC [JOIN_UNIT_LEFT] THEN
    MESON_TAC [option_INJ; PAIR_EQ];
    ALL_TAC] THEN
  (* Lift f ft2 = SOME (b2, UNIT) to f h = SOME (b2, rm2) *)
  SUBGOAL_THEN `(f:RES->(A#RES)option) h = SOME (b2, rm2:RES)` ASSUME_TAC THENL [
    FIRST_X_ASSUM (MP_TAC o SPECL [`ft2:RES`; `b2:A`; `UNIT:RES`; `rm2:RES`; `h:RES`]) THEN
    ASM_REWRITE_TAC [JOIN_UNIT_LEFT] THEN
    MESON_TAC [option_INJ; PAIR_EQ];
    ALL_TAC] THEN
  (* f h determines unique output: b1 = b2, rm1 = rm2 *)
  SUBGOAL_THEN `b1:A = b2 /\ rm1:RES = rm2` STRIP_ASSUME_TAC THENL [
    ASM_MESON_TAC [option_INJ; PAIR_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  (* JOIN cancellation: ft1 = ft2 *)
  SUBGOAL_THEN `JOIN (SOME ft1) (SOME rm1) = JOIN (SOME ft2) (SOME rm1) /\
                IS_SOME (JOIN (SOME ft1) (SOME rm1))` MP_TAC THENL [
    ASM_REWRITE_TAC [IS_SOME_SOME]; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o MATCH_MP JOIN_CANCEL_RIGHT) THEN
  MESON_TAC [option_INJ]
);;

(* Under IS_FUNCTIONAL, the two epsilon selections are consistent. *)
let FUNCTIONAL_SELECT = prove(
  `!P:A->RES->bool. !h:RES.
     IS_FUNCTIONAL P /\ (?b ft. P b ft /\ IS_SUB ft h) ==>
     P (@b. ?ft. P b ft /\ IS_SUB ft h)
       (@ft. ?b. P b ft /\ IS_SUB ft h) /\
     IS_SUB (@ft. ?b. P b ft /\ IS_SUB ft h) h`,
  REPEAT GEN_TAC THEN REWRITE_TAC [IS_FUNCTIONAL_DEF] THEN MESON_TAC []
);;

(* Characterize TO_MSL success: extract the witnessing footprint. *)
let TO_MSL_SPEC = prove(
  `!P:A->RES->bool. !h b rm.
     IS_FUNCTIONAL P /\ TO_MSL P h = SOME (b, rm) ==>
     ?ft. P b ft /\ IS_SUB ft h /\ rm = REMOVE h ft`,
  REPEAT GEN_TAC THEN REWRITE_TAC [TO_MSL_DEF] THEN
  COND_CASES_TAC THENL [ALL_TAC; MESON_TAC [option_DISTINCT]] THEN
  REWRITE_TAC [option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
  EXISTS_TAC `@ft:RES. ?b:A. P b ft /\ IS_SUB ft h` THEN
  MP_TAC (SPECL [`P:A->RES->bool`; `h:RES`] FUNCTIONAL_SELECT) THEN
  ASM_MESON_TAC []);;

(* Introduce TO_MSL success from a known footprint. *)
let TO_MSL_INTRO = prove(
  `!P:A->RES->bool. !h b ft.
     IS_FUNCTIONAL P /\ P b ft /\ IS_SUB ft h ==>
     TO_MSL P h = SOME (b, REMOVE h ft)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [TO_MSL_DEF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?b:A ft:RES. P b ft /\ IS_SUB ft h` (fun th -> REWRITE_TAC [th]) THENL [
    ASM_MESON_TAC []; ALL_TAC] THEN
  MP_TAC (SPECL [`P:A->RES->bool`; `h:RES`] FUNCTIONAL_SELECT) THEN
  ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
  REWRITE_TAC [option_INJ; PAIR_EQ] THEN
  UNDISCH_TAC `IS_FUNCTIONAL (P:A->RES->bool)` THEN
  REWRITE_TAC [IS_FUNCTIONAL_DEF] THEN DISCH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`h:RES`;
    `(@b:A. ?ft. P b ft /\ IS_SUB ft h)`; `b:A`;
    `(@ft:RES. ?b:A. P b ft /\ IS_SUB ft h)`; `ft:RES`]) THEN
  ASM_MESON_TAC []);;

(* Direction 2: every functional SL predicate induces a valid MSL computation. *)
let TO_MSL_VALID = prove(
  `!P:A->RES->bool. IS_FUNCTIONAL P ==> IS_VALID_MSL (TO_MSL P)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [IS_VALID_MSL_DEF] THEN CONJ_TAC THENL [
    (* Substate: REMOVE h ft <= h *)
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`P:A->RES->bool`; `h:RES`; `b:A`; `rm:RES`] TO_MSL_SPEC) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`h:RES`; `ft:RES`] REMOVE_THM) THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC [IS_SUB_DEF; JOIN_COMM];

    (* Frame preservation *)
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`P:A->RES->bool`; `h:RES`; `b:A`; `rm:RES`] TO_MSL_SPEC) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    (* ft <= h <= h', so TO_MSL P h' succeeds with same (b, ft) *)
    SUBGOAL_THEN `IS_SUB ft h'` ASSUME_TAC THENL [
      ASM_MESON_TAC [IS_SUB_TRANS; IS_SUB_DEF]; ALL_TAC] THEN
    MP_TAC (SPECL [`P:A->RES->bool`; `h':RES`; `b:A`; `ft:RES`] TO_MSL_INTRO) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    EXISTS_TAC `REMOVE h' ft` THEN ASM_REWRITE_TAC [] THEN
    (* JOIN (REMOVE h ft) frm = REMOVE h' ft by assoc + cancellation *)
    MP_TAC (SPECL [`h:RES`; `ft:RES`] REMOVE_THM) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`h':RES`; `ft:RES`] REMOVE_THM) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`SOME (ft:RES)`;
      `JOIN (SOME (REMOVE h ft)) (SOME frm)`;
      `SOME (REMOVE h' ft)`] JOIN_CANCEL_LEFT) THEN
    ANTS_TAC THENL [
      REWRITE_TAC [GSYM JOIN_ASSOC] THEN ASM_REWRITE_TAC [IS_SOME_SOME];
      ASM_MESON_TAC [option_INJ]]
  ]);;
