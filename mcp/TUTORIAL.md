# HOL Light MCP Tutorial

Worked examples of increasing difficulty, showing different proof techniques.

## 1. Commutativity of conjunction

A one-shot proof — `STRIP_TAC` decomposes the goal, `ASM_REWRITE_TAC` finishes it.

```
set_goal  "`!p q. p /\ q ==> q /\ p`"
→ {"goals":[{"hypotheses":[],"conclusion":"forall p q. p /\\ q ==> q /\\ p"}], ...}

apply_tactic  "REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]"
→ {"proved":true,"theorem":"|- forall p q. p /\\ q ==> q /\\ p"}
```

## 2. EVEN squares

Using `search_theorems` to find a lemma, then rewriting with it.

```
set_goal  "`!n. EVEN n ==> EVEN(n * n)`"

apply_tactic  "GEN_TAC THEN STRIP_TAC"
→ hypotheses: ["EVEN n"],  conclusion: "EVEN (n * n)"

search_theorems  name="EVEN_MULT"
→ [{"name":"EVEN_MULT","statement":"|- forall m n. EVEN (m * n) <=> EVEN m \\/ EVEN n"}]

apply_tactic  "ASM_REWRITE_TAC[EVEN_MULT]"
→ proved
```

## 3. Gauss sum by induction

Proving `∑ᵢ₌₀ⁿ i = n(n+1)/2`. Induction creates two subgoals — base case and step.

```
set_goal  "`!n. nsum(0..n) (\i. i) = (n * (n + 1)) DIV 2`"

apply_tactic  "INDUCT_TAC"
→ 2 subgoals:
  [0] conclusion: "nsum (0..0) (\i. i) = (0 * (0 + 1)) DIV 2"
  [1] hypotheses: ["nsum (0..n) (\i. i) = (n * (n + 1)) DIV 2"]
      conclusion: "nsum (0..SUC n) (\i. i) = (SUC n * (SUC n + 1)) DIV 2"
```

Base case — expand nsum and compute:
```
apply_tactic  "REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC"
→ 1 subgoal remaining (inductive step)
```

Inductive step — expand nsum, apply IH, arithmetic:
```
apply_tactic  "REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ASM_REWRITE_TAC[LE_0] THEN ARITH_TAC"
→ proved: |- forall n. nsum (0..n) (\i. i) = (n * (n + 1)) DIV 2
```

## 4. Backtracking

When a tactic doesn't help, `backtrack` undoes it.

```
set_goal  "`!n. 0 < n ==> (n - 1) + 1 = n`"

apply_tactic  "REWRITE_TAC[ADD_SUB]"
→ goal unchanged (wrong lemma — ADD_SUB is `n + m - m = n`)

backtrack  steps=1

apply_tactic  "ARITH_TAC"
→ proved
```

## 5. Composition of injections

Pure first-order logic — `MESON_TAC` handles it automatically.

```
set_goal  "`!f g. (!x y. f x = f y ==> x = y) /\ (!x y. g x = g y ==> x = y)
                  ==> (!x y. g(f x) = g(f y) ==> x = y)`"

apply_tactic  "MESON_TAC[]"
→ proved
```

## 6. Product of consecutive numbers is even

Case splitting on parity, with lemma search.

```
set_goal  "`!n. (n * (n + 1)) MOD 2 = 0`"
```

First, find relevant theorems:
```
search_theorems  name="EVEN_MOD"
→ [{"name":"EVEN_MOD","statement":"|- forall n. EVEN n <=> n MOD 2 = 0"}, ...]

search_theorems  name="EVEN_MULT"
→ [{"name":"EVEN_MULT","statement":"|- forall m n. EVEN (m * n) <=> EVEN m \\/ EVEN n"}]

search_theorems  name="EVEN_OR_ODD"
→ [{"name":"EVEN_OR_ODD","statement":"|- forall n. EVEN n \\/ ODD n"}]
```

Strategy: rewrite `MOD 2 = 0` to `EVEN`, then case split on whether `n` is even or odd.

```
apply_tactic  "GEN_TAC THEN REWRITE_TAC[GSYM EVEN_MOD; EVEN_MULT] THEN DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THEN ASM_REWRITE_TAC[]"
→ hypotheses: ["ODD n"],  conclusion: "EVEN n \\/ EVEN (n + 1)"
```

When `n` is even, the left disjunct is immediate. When `n` is odd, we need `EVEN(n+1)`:

```
search_theorems  name="EVEN_ADD"
→ [{"name":"EVEN_ADD","statement":"|- forall m n. EVEN (m + n) <=> EVEN m <=> EVEN n"}]

search_theorems  name="NOT_EVEN"
→ [{"name":"NOT_EVEN","statement":"|- forall n. ~EVEN n <=> ODD n"}]

apply_tactic  "DISJ2_TAC THEN REWRITE_TAC[EVEN_ADD] THEN ASM_REWRITE_TAC[NOT_EVEN; ARITH]"
→ proved: |- forall n. (n * (n + 1)) MOD 2 = 0
```

## Proof workflow summary

1. **set_goal** — state the theorem
2. **goal_state** — inspect hypotheses and conclusion
3. **search_theorems** — find relevant lemmas
4. **apply_tactic** — try automation first (`ARITH_TAC`, `MESON_TAC[]`), then targeted tactics
5. **backtrack** — undo if a tactic didn't help
6. Repeat until `"proved":true`
7. **hol_status** — check if HOL Light is alive (useful for debugging)
8. **hol_restart** — restart HOL Light if it has died or is in a bad state

---

## s2n-bignum ARM proofs

The following examples prove properties of AArch64 machine code using the s2n-bignum framework. They require a checkpoint with `arm/proofs/base.ml` preloaded (see README).

## 7. Straight-line: add and subtract

Two instructions (`add x2, x1, x0; sub x2, x2, x1`) — proves `x2 = x0`.

```
eval  'let simple_mc = new_definition `simple_mc = [
    word 0x22; word 0x00; word 0x00; word 0x8b;
    word 0x42; word 0x00; word 0x01; word 0xcb
  ]:((8)word)list`;;
let EXEC = ARM_MK_EXEC_RULE simple_mc'

set_goal  "`forall pc a b.
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) simple_mc /\
         read PC s = word pc /\ read X0 s = word a /\ read X1 s = word b)
    (\s. read PC s = word (pc+8) /\ read X2 s = word a)
    (MAYCHANGE [PC;X2])`"

apply_tactic  "REPEAT STRIP_TAC THEN ENSURES_INIT_TAC \"s0\""
apply_tactic  "ARM_STEPS_TAC EXEC (1--2)"
apply_tactic  "ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE"
→ proved
```

## 8. Conditional branch: max(x1, x2)

A program with `cmp; b.hi` that copies `max(x1, x2)` to `x0`. Requires case splitting on the branch condition.

```
eval  'let branch_mc = new_definition `branch_mc = [
    word 0x3f; word 0x00; word 0x02; word 0xeb;
    word 0x68; word 0x00; word 0x00; word 0x54;
    word 0xe0; word 0x03; word 0x02; word 0xaa;
    word 0xc0; word 0x03; word 0x5f; word 0xd6;
    word 0xe0; word 0x03; word 0x01; word 0xaa;
    word 0xc0; word 0x03; word 0x5f; word 0xd6
  ]:((8)word)list`;;
let EXEC = ARM_MK_EXEC_RULE branch_mc'

set_goal  "`forall pc pcret a b.
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) branch_mc /\
         read X30 s = word pcret /\ read PC s = word pc /\
         read X1 s = word a /\ read X2 s = word b)
    (\s. read PC s = word pcret /\ read X0 s = word_umax (word a) (word b))
    (MAYCHANGE [PC;X0] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`"
```

Execute up to the branch, then case split:
```
apply_tactic  "REPEAT STRIP_TAC THEN REWRITE_TAC[SOME_FLAGS] THEN ENSURES_INIT_TAC \"s0\" THEN ARM_STEPS_TAC EXEC (1--2)"

apply_tactic  "FIRST_X_ASSUM MP_TAC THEN COND_CASES_TAC THENL [
  POP_ASSUM (LABEL_TAC \"Hcond\") THEN DISCH_TAC THEN
  ARM_STEPS_TAC EXEC (3--4) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN \"Hcond\" MP_TAC THEN REWRITE_TAC[WORD_UMAX;VAL_WORD_SUB_EQ_0] THEN ARITH_TAC;
  POP_ASSUM (LABEL_TAC \"Hcond\") THEN DISCH_TAC THEN
  ARM_STEPS_TAC EXEC (3--4) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN \"Hcond\" MP_TAC THEN REWRITE_TAC[WORD_UMAX;VAL_WORD_SUB_EQ_0] THEN ARITH_TAC]"
→ proved
```

## 9. Loop with invariant: count to 20

A loop that increments x1 by 1 and x0 by 2 until x1=10, proving x0=20. Uses `ENSURES_WHILE_PAUP_TAC` for the loop invariant.

```
eval  'let loop_mc = new_definition `loop_mc = [
  word 0xe1; word 0x03; word 0x1f; word 0xaa;
  word 0xe0; word 0x03; word 0x1f; word 0xaa;
  word 0x21; word 0x04; word 0x00; word 0x91;
  word 0x00; word 0x08; word 0x00; word 0x91;
  word 0x3f; word 0x28; word 0x00; word 0xf1;
  word 0xa1; word 0xff; word 0xff; word 0x54;
  word 0xc0; word 0x03; word 0x5f; word 0xd6
]:((8)word)list`;;
let EXEC = ARM_MK_EXEC_RULE loop_mc'

set_goal  "`forall pc retpc.
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) loop_mc /\
         read PC s = word pc /\ read X30 s = word retpc)
    (\s. read PC s = word retpc /\ read X0 s = word 20)
    (MAYCHANGE [PC;X0;X1] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`"
```

Declare the loop with invariant `x1 = i, x0 = 2*i`:
```
apply_tactic  "REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_WHILE_PAUP_TAC `0` `10` `pc + 8` `pc + 0x14`
    `\\i s. (read X1 s = word i /\\ read X0 s = word (i*2) /\\ read X30 s = word retpc) /\\
           (read ZF s <=> i = 10)`"
```

Solve the preamble, backedge, and exit (leaving loop body):
```
apply_tactic  "REPEAT CONJ_TAC THENL [
  ARITH_TAC;
  ARM_SIM_TAC EXEC (1--2) THEN CONV_TAC WORD_RULE;
  ALL_TAC;
  REPEAT STRIP_TAC THEN ARM_SIM_TAC EXEC [1];
  ARM_SIM_TAC EXEC (1--2) THEN CONV_TAC WORD_RULE]"
```

Prove the loop body — simulate 3 instructions, then word arithmetic:
```
apply_tactic  "REPEAT STRIP_TAC THEN ARM_SIM_TAC EXEC (1--3) THEN REPEAT CONJ_TAC THENL [
  CONV_TAC WORD_RULE;
  CONV_TAC WORD_RULE;
  REWRITE_TAC[WORD_BLAST `word_add x (word 18446744073709551607):int64 = word_sub x (word 9)`] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN REWRITE_TAC[VAL_WORD;DIMINDEX_64] THEN
  IMP_REWRITE_TAC[MOD_LT; ARITH_RULE`9 < 2 EXP 64`] THEN CONJ_TAC THEN ASM_ARITH_TAC]"
→ proved
```
