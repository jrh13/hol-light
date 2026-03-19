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
