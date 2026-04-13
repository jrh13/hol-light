---
name: hol-light
description: Prove theorems in HOL Light via MCP tools. Use when the user asks to prove a theorem, verify a proof, or work with HOL Light tactics, goals, or lemmas.
compatibility: Requires the hol-light MCP server running (uv run hol-light-mcp).
---

# HOL Light MCP — LLM Skill Guide

You have access to a HOL Light theorem prover via MCP tools. This document teaches you how to use them effectively.

HOL Light is a classical higher-order logic theorem prover. The law of excluded middle is available, and proof by contradiction is fine. Only use `(* ... *)` for OCaml comments.

## Proof workflow

**One-shot proofs:** If you know the full tactic, use **prove**(goal, tactic) to get the theorem in a single call.

**Interactive proofs:**
1. **set_goal** — state the theorem to prove
2. **goal_state** — inspect current goals (check hypotheses and conclusion)
3. **search_theorems** — find relevant lemmas by name substring
4. **apply_tactic** — apply a tactic; check response for `"proved":true`
5. **apply_tactics** — apply multiple tactics in one round-trip (faster for straightforward sequences)
6. **backtrack** — undo if a tactic made things worse
7. Repeat 2–6 until proved
8. **hol_status** — check if HOL Light is alive (useful for debugging)
9. **hol_restart** — restart HOL Light if it has died or is in a bad state

Always read the goal state carefully before choosing a tactic. The structured JSON tells you exactly what hypotheses you have and what you need to show.

## Core tactics

### Logical structure
| Tactic | Use when |
|--------|----------|
| `GEN_TAC` | Goal is `!x. P(x)` — strips one universal quantifier |
| `X_GEN_TAC \`n:num\`` | Like `GEN_TAC` but names the variable |
| `STRIP_TAC` | Goal has `==>`, `/\`, or `!` at the top — strips one connective |
| `REPEAT STRIP_TAC` | Strip all top-level connectives at once |
| `CONJ_TAC` | Goal is `P /\ Q` — splits into two subgoals |
| `DISJ1_TAC` / `DISJ2_TAC` | Goal is `P \/ Q` — choose which disjunct to prove |
| `EQ_TAC` | Goal is `P <=> Q` — splits into `P ==> Q` and `Q ==> P` |
| `DISCH_TAC` | Move antecedent of `P ==> Q` into hypotheses |
| `EXISTS_TAC \`witness\`` | Goal is `?x. P(x)` — provide the witness |

### Rewriting
| Tactic | Use when |
|--------|----------|
| `REWRITE_TAC[thm1; thm2]` | Rewrite goal using equations (left-to-right) |
| `ASM_REWRITE_TAC[thms]` | Rewrite using hypotheses AND given theorems |
| `ONCE_REWRITE_TAC[thm]` | Rewrite only once (avoids looping) |
| `GEN_REWRITE_TAC I [thm]` | Rewrite at top level only |
| `SIMP_TAC[thms]` | Conditional rewriting (handles side conditions) |
| `ASM_SIMP_TAC[thms]` | Conditional rewriting with hypotheses |

### Automation
| Tactic | Solves |
|--------|--------|
| `ARITH_TAC` | Linear arithmetic over naturals and integers |
| `REAL_ARITH_TAC` | Linear arithmetic over reals |
| `MESON_TAC[thms]` | First-order logic with given lemmas |
| `ASM_MESON_TAC[thms]` | First-order logic with hypotheses + lemmas |
| `TAUT` (as a rule) | Propositional tautologies: `TAUT \`p /\ q ==> q\`` |
| `SET_TAC[thms]` | Set-theoretic goals |
| `RING_TAC` | Ring equalities |
| `WORD_RULE` | Word (bitvector) equalities |
| `CONV_TAC WORD_RULE` | Word equalities as a tactic |

### Induction
| Tactic | Use when |
|--------|----------|
| `INDUCT_TAC` | Induction on the outermost `!n.` (natural number) |
| `LIST_INDUCT_TAC` | Induction on a list |
| `MATCH_MP_TAC thm` | Apply a theorem backwards (modus ponens in reverse) |

### Hypothesis management
| Tactic | Effect |
|--------|--------|
| `ASM_REWRITE_TAC[]` | Rewrite goal using all hypotheses |
| `FIRST_X_ASSUM MATCH_MP_TAC` | Use first matching hypothesis backwards (consumes it) |
| `FIRST_ASSUM MATCH_MP_TAC` | Same but keeps the hypothesis |
| `UNDISCH_TAC \`term\`` | Move a hypothesis back to the goal as antecedent |
| `SUBGOAL_THEN \`P\` ASSUME_TAC` | Assert and prove an intermediate fact |

### Combinators
| Combinator | Meaning |
|------------|---------|
| `tac1 THEN tac2` | Apply tac1, then tac2 to all resulting subgoals |
| `tac1 THENL [tac2; tac3]` | Apply tac1, then tac2 to first subgoal, tac3 to second |
| `REPEAT tac` | Apply tac repeatedly until it fails |
| `TRY tac` | Try tac, succeed even if it fails |

## Searching for theorems

`search_theorems` searches by name substring. The search is cheap — use it freely. Tips:
- Search for the main constant: `search_theorems name="EVEN"` for theorems about `EVEN`
- Search for the operation: `search_theorems name="ADD"` for addition theorems
- Common prefixes: `ADD_`, `MULT_`, `LE_`, `LT_`, `EVEN_`, `ODD_`, `DIV_`, `MOD_`
- For rewriting, look for theorems with `<=>` or `=` in the statement

You can also use `eval` for more powerful searches:
```
eval  'search [`EVEN`]'       -- search by subterm pattern
eval  'search [`EVEN`; `ODD`]' -- multiple patterns
```

## Common proof patterns

### Prove by simplification
```
apply_tactic  "SIMP_TAC[thm1; thm2; thm3]"
```

### Prove by rewriting then arithmetic
```
apply_tactic  "REWRITE_TAC[DEF1; DEF2] THEN ARITH_TAC"
```

### Prove by induction
```
apply_tactic  "INDUCT_TAC"          -- creates base case + inductive step
apply_tactic  "base case tactic"    -- solve base case
apply_tactic  "ASM_REWRITE_TAC[...] THEN inductive step tactic"
```

### Prove using a key lemma
```
search_theorems  name="KEY_LEMMA"
apply_tactic  "MATCH_MP_TAC KEY_LEMMA THEN ..."
```

### Case split
```
apply_tactic  "ASM_CASES_TAC `P` THEN ASM_REWRITE_TAC[]"
```

### Declarative sub-lemma
```
apply_tactic  "SUBGOAL_THEN `intermediate_fact` ASSUME_TAC"
-- prove the sub-lemma first, then use it
```

## Pitfalls

- **`REWRITE_TAC[GSYM thm]` can loop.** Use `ONCE_REWRITE_TAC[GSYM thm]` instead.
- **`FIRST_X_ASSUM` consumes the hypothesis.** Use `FIRST_ASSUM` when you need to reuse it.
- **`ASM_ARITH_TAC` hangs with many assumptions.** Discard irrelevant ones first with `REPEAT (FIRST_X_ASSUM (K ALL_TAC))` or targeted `UNDISCH_TAC` + `DISCH_TAC`.
- **`WORD_RULE` hangs on `val(word(...))`.** Normalize via `VAL_WORD_EQ` first.
- **Natural number subtraction is truncating.** `n - m = 0` when `m >= n`. Use `ARITH_TAC` for goals involving subtraction.
- **`*` is right-associative for `num`.** Use explicit parentheses to avoid surprises.
- **When a tactic hangs**, backtrack and try a different approach. Automation tactics (`MESON_TAC`, `ARITH_TAC`) can diverge on hard goals.

## s2n-bignum ARM proof tactics

For proving properties of AArch64 machine code (requires `arm/proofs/base.ml`):

| Tactic | Use when |
|--------|----------|
| `ARM_MK_EXEC_RULE mc` | Decode a machine code byte list into instruction theorems |
| `ENSURES_INIT_TAC "s0"` | Initialize symbolic state for an `ensures` proof |
| `ARM_STEPS_TAC EXEC (1--n)` | Symbolically execute n instructions |
| `ARM_SIM_TAC EXEC (1--n)` | INIT + STEPS + FINAL in one shot |
| `ENSURES_FINAL_STATE_TAC` | Close postcondition and frame |
| `ENSURES_WHILE_PAUP_TAC a b pc_body pc_back inv` | Declare a counting-up loop with invariant |
| `COND_CASES_TAC` | Case split on a conditional branch |
| `CONV_TAC WORD_RULE` | Solve word (bitvector) equalities |
| `WORD_BLAST` | Bit-blasting for word goals |

Typical ARM proof pattern:
```
REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
ARM_STEPS_TAC EXEC (1--n) THEN
ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
CONV_TAC WORD_RULE
```

## Utility tools

- **hol_type** — get the type of a HOL Light term (e.g., `hol_type` with term `` `1 + 1` `` returns `num`)
- **hol_load** — load a HOL Light file via `needs` (e.g., `hol_load` with file `"Library/words.ml"`)
- **hol_interrupt** — send SIGINT to cancel a hung tactic (e.g., when `MESON_TAC` diverges)
- **hol_help** — return this tactic reference (SKILL.md). Call before your first proof.
- **start_recording** — record all tactic applications to a JSONL file for later replay
- **stop_recording** — stop recording and return the file path

## General advice

- **Try automation first.** `ARITH_TAC`, `MESON_TAC[]`, or `ASM_MESON_TAC[]` often solve goals outright.
- **Read the goal.** The JSON tells you exactly what you have (hypotheses) and what you need (conclusion). Don't guess.
- **Search before you rewrite.** Use `search_theorems` to find the right lemma name rather than guessing.
- **Backtrack freely.** If a tactic doesn't simplify the goal, undo it and try something else.
- **Strip first.** `REPEAT STRIP_TAC` is almost always a good opening move.
- **`ASM_REWRITE_TAC[]` is your friend.** It rewrites with all hypotheses. Use it after `STRIP_TAC`.
- **Work incrementally.** Apply one tactic at a time, inspect the goal state, then proceed.
- **Use `SUBGOAL_THEN` for declarative proofs.** Clear intermediate goals make proofs easier to follow.
- **Structure longer proofs into smaller lemmas.** It's fine for a proof to have 100+ tactic steps, but breaking into lemmas is preferred.
- **Avoid exotic tactics** unless you know they're needed.
