# HOL Light MCP — LLM Skill Guide

You have access to a HOL Light theorem prover via MCP tools. This document teaches you how to use them effectively.

## Proof workflow

1. **set_goal** — state the theorem to prove
2. **goal_state** — inspect current goals (check hypotheses and conclusion)
3. **search_theorems** — find relevant lemmas by name substring
4. **apply_tactic** — apply a tactic; check response for `"proved":true`
5. **backtrack** — undo if a tactic made things worse
6. Repeat 2–5 until proved

Always read the goal state carefully before choosing a tactic. The structured JSON tells you exactly what hypotheses you have and what you need to show.

## Core tactics

### Logical structure
| Tactic | Use when |
|--------|----------|
| `GEN_TAC` | Goal is `!x. P(x)` — strips one universal quantifier |
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
| `FIRST_X_ASSUM MATCH_MP_TAC` | Use first matching hypothesis backwards |
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

`search_theorems` searches by name substring. Tips:
- Search for the main constant: `search_theorems name="EVEN"` for theorems about `EVEN`
- Search for the operation: `search_theorems name="ADD"` for addition theorems
- Common prefixes: `ADD_`, `MULT_`, `LE_`, `LT_`, `EVEN_`, `ODD_`, `DIV_`, `MOD_`
- For rewriting, look for theorems with `<=>` or `=` in the statement

You can also use `eval` for more complex searches:
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

## Tips

- **Try automation first.** `ARITH_TAC`, `MESON_TAC[]`, or `ASM_MESON_TAC[]` often solve goals outright.
- **Read the goal.** The JSON tells you exactly what you have (hypotheses) and what you need (conclusion). Don't guess.
- **Search before you rewrite.** Use `search_theorems` to find the right lemma name rather than guessing.
- **Backtrack freely.** If a tactic doesn't simplify the goal, undo it and try something else.
- **Strip first.** `REPEAT STRIP_TAC` is almost always a good opening move — it puts all hypotheses into the context.
- **Natural number subtraction is truncating.** `n - m = 0` when `m >= n`. Use `ARITH_TAC` for goals involving subtraction.
- **`ASM_REWRITE_TAC[]` is your friend.** It rewrites with all hypotheses. Use it after `STRIP_TAC`.
