# Efficiency notes:
  proof-producing evaluation of the 4CT reducibility check in HOL Light
(written 2026-10-05; data from CHANGES_part1_eval_01.md, CHANGES_u8_eval_01.md,
CHANGES_birkhoff_eval_01.md and the logs cited below.  All numbers measured on
the 32-core AMD EPYC 9R45 box, OCaml 4.14.1, HOL Light commit 72f2059.)

(Package edition note: the file names in this document are those of the
development tree.  In the package,
part1_eval_dev/part1_fo_dev/part1_fo2_dev/part1_fo3_dev.ml are merged into
part2_eval.ml, part1_compiled_fo3.hl is part2_compiled.hl, part1_run.ml and
part1_final.ml are part2_run.ml and part2_final.ml, part1_compile_fo3.ml is
part2_compile.ml.  The development tree called the computation 'Part 1' and the
mathematics 'Part 2'; the package's make.ml numbers them the other way round.)

## 1. What is being computed
`check_reducible cf` for the 633 configurations (configurations.ml = Coq
configurations.v): for each cf, `kempe_tree (cfprog cf)` (Kempe-closure tree
over the ring colourings: ctree/gtree restriction iterated `ring size` times)
and `contract_ctree cf`, then disjointness.  The theorem produced is
`|- check_reducible cfNNN <=> T`, by kernel inference only (no reflection, no
mk_thm).  `reducibility` (four_color.ml) is
`!cf. MEM cf the_configs ==> check_reducible cf`; with all 633 results,
part1_final.ml proves it by REWRITE (ALL_MEM, the_configs, ALL) and
FOUR_COLOR = MP FOUR_COLOR_HYPERMAP REDUCIBILITY. Reference point: check4ct_v5
(plain OCaml, unverified, same algorithm) does all 633 in 255 s
(memory/check4ct_v5_times_20261004.log; max 2.2 s for cf281).

## 2. The evaluator: Solovyev's eval_compile (~/compute-hol-light)
Each HOL definition becomes an OCaml function `f_c args opt_th` that
INSTantiates the clause theorem with the evaluated arguments and chains with
TRANS/MK_COMB; i.e. one small inference per rewrite step, compiled OCaml
control flow. Constraints: first-order constructor patterns, no lambdas/partial
applications as arguments, no 0-ary non-constructor constants as values, no
`?`/`@`/`match` (handled by proven reformulations in part1_eval_dev.ml:
eta-expanded `_e` forms, NUM forms for SUC recursion, `zx` zero-ary expansion,
option-valued helpers, cpcol for ITLIST cpcolor1, ...). The compute.ml CBV
engine (used for the_quiz_tree / the_dbound1_check / exclude5..11 /
birkhoff2-5) is slower per rewrite (~20 us) but needs no code generation.

## 3. The optimisation history (bytecode unless stated)
| stage | all-633 estimate | what changed |
|---|---|---|
| original eval_compile pipeline (March) | ~35 days
  | ring-10 configs > 45 min each |
| 2026-10-04 17:55 first end-to-end: cf001 0.40 s, cf002 3.7 s, cf003 363 s
  | (weeks) | cf003 ring 8 alone 6 min |
| fo layer (part1_fo_dev.ml): cf003 1.53 s (237x) | ~13.5 days
  | kernel INST pathology removed (Sec. 4) |
| fo2 layer (part1_fo2_dev.ml): cf003 0.81, cf017 23, cf033 7.8 s
  | ~3.3 days (= 78 h, measured by the sweep) | step count cut 2.45x (Sec. 5) |
| native compilation of the same code | ~14 h | 5.6x (Sec. 6) |
Final run: p1v3_native 1 633 started 2026-10-04 19:47 UTC (1 h 43 min to load
the whole formalization natively incl. the unavoidability case analysis),
checks began 21:30, ETA ~11:40 UTC 2026-10-05.

## 4. Root cause #1: lambdas in instantiated theorems (300000x)
Profiling cf003 (ring 8; trees of 2k-10k term nodes): gtree_restrict 65 s,
ctree_restrict 285 s, while the OCaml checker does the whole config in 1 ms.
Microbenchmark: INST of a 4-level-lambda pattern with four 2153-node tree
arguments = 970 us; the same pattern without the lambda = 4.3 us.  HOL Light's
kernel `vsubst` performs the capture-avoidance check
`exists (fun (t,x) -> vfree_in v t && vfree_in x s)` at EVERY Abs, and
`vfree_in v t` walks the entire instantiated argument.  Gonthier's definitions
are CPS-heavy (gtr_split/ctr_split continuations,
case_ctree_node/case_gtree_node function arguments, ctr_decr's continuation,
LET-lambdas), so every call paid O(size of all tree arguments). Fix
(part1_fo_dev.ml, 271 ln): defunctionalised equivalents proven equal to the
originals -- accumulator tuples with FST/SND helpers (gtr_split4/ctr_split3),
constructor-case gtr_match*_t, ctree_restrict_node/ctree_restrict_split,
ktc_apply, kempe_tree_h; eval_compile db p2_build_db_fo.  (The earlier
hypothesis "ktc_step evaluates ctree_restrict twice" was WRONG: eval_compile
flattens LET anyway and the duplication is only a factor 2.) General lesson: a
proof-producing evaluator must never INST a theorem containing a lambda with
large argument terms.

## 5. Root cause #2: step count (fo2, 2.45x fewer calls)
count_hl.py instruments every generated function.  cf033 with fo rules = 6.29M
calls: the leaf decrement chain ctr_e_decr -> gtree_sub -> match_count_fn ->
gtree_mem -> gtree_leaf_mem (+ colour/gram-symbol equality tests) 35%,
gtr_cons/ctr_cons emptiness tests 10%, FST/SND projections 8%.
part1_fo2_dev.ml: cons-by-constructor cases, tuple PATTERNS instead of
projections (eval_compile accepts `(a,b,c)` argument patterns), cdec1/2/3 with
their 90 (bit_stack x gtree-constructor) clauses pre-evaluated by REWRITE_CONV.
cf033: 6.29M -> 2.57M calls, 22.3 -> 7.8 s. Remaining profile is flat
(ctree_empty 9%, gtr_cons 8%, ctr_cons 7%, each one step): diminishing returns.
Per-step cost (cf017, wrappers around the kernel): INST 29.5M calls 1.45 us
each, MK_COMB 40.8M 0.55 us, TRANS 22.7M 0.64 us, REFL 37.1M 0.30 us => ~25M
steps, ~130M kernel ops; the primitives are cheap, the count is the cost.

## 6. Native compilation (hol.sh inline-load / compile / link, hol_lib.cmxa)
Same generated code compiled by ocamlopt: 5.62x aggregate over 305 common
configs (per config 5.29..6.39, median 5.71); loads the formalization 4x faster
too (9 min vs 35 min; ~100 min for the unavoidability CBV vs ~13 h bytecode).
Recipe/gotchas: memory/native_build.md (dedupe repeated inlinings; strip
`#load "str.cma"`; `-I +str`/`-package str`; inline-load's relative `needs`
resolve against the CURRENT DIRECTORY; the native core library hol_lib.cmxa
must be rebuilt when the core sources change -- it was 4 months stale here,
breaking Multivariate natively).

## 7. Measured comparison
   (305 configurations evaluated by both the bytecode sweep and the native run)
| | OCaml checker (unverified) | HOL bytecode | HOL native |
|---|---|---|---|
| total 305 configs | 108.5 s | 119,322 s (33.1 h) | 21,244 s (5.9 h) |
| ratio to OCaml | 1 | 1100x | 196x |
| examples cf017 / cf110 / cf281 | 0.018 / 1.33 / 2.21 s | 23 / 1427 / 2018 s
  | 3.8 / 270 / 352 s |
All 633 in bytecode (20-process sweep, 2026-10-04 19:50 - 2026-10-05 00:30):
281,327 s CPU = 78.1 h, every result `true`, 0 errors
(memory/part1_sweep_<k>_of_20_20261004_1848.log) -- an independent bytecode
cross-check of every per-configuration result of the native run.

## 8. Things that did NOT help (measured)
- Memoising f_ctree_restrict/f_gtree_restrict on the DAG-shared trees
  (memoize_hl.py): 43% hit rate, only 6-7% faster.
- GC tuning (minor heap 8M words, space_overhead 200): 0% in an interleaved
  A/B; a 2.7x "win" seen once was ambient variance on the loaded box.
- For the unavoidability CBV (exclude5..11): replacing the 225-rule cmp_range
  table by an O(1) Hashtbl conversion: 8%; the cost there is the rewrite count
  of hubcap_fit/cmp_part at compute.ml's ~20 us/rewrite (cf. exclude6: 236
  Hubcap checks = 188 s bytecode).  An eval_compile port of part/hubcap/redpart
  (~3-4 us/step) should give ~5x on the ~100-minute native unavoidability
  phase; deferred.
- Earlier (CBV side): rewrite-count reductions (fitqa table, equality conv,
  NUM-form rules) gave nothing; the win there was never expanding the 87k-node
  quiz tree (symbolic lookup rules, 100x on redpart) and compute_fast.ml (one
  INST per rule instead of a SPEC chain, 1.6-2.4x).

## 9. Where the remaining 196x (native) over plain OCaml goes
Each evaluation step builds and checks a theorem: ~5 kernel operations (INST of
the clause, MK_COMB per argument, TRANS, REFL) each allocating terms and doing
type checks; the OCaml checker does one pattern match and one allocation.
Further reductions would need a leaner code generator (e.g. a single pre-proved
`|- c = T ==> (if c then x else y) = x` MP instead of MK_COMB x3 + INST + TRANS
x2 per conditional), fewer but bigger rules (pre-evaluated tables as in cdec),
or a trusted-kernel extension (reflection), which this project deliberately
does not use.

## 10. Final totals (run completed 2026-10-05 11:22 UTC)
Native single process (p1v3_native): 633 checks in 49,887 s = 13.86 h (plus 1 h
43 min to load the formalization); bytecode sweep of the same 633: 281,327 s =>
bytecode/native = 5.64x overall; native/OCaml-checker = 195x. Result:
`|- reducibility` and
`|- !H. planar_hypermap H /\ bridgeless H ==> four_colorable H` (no
hypotheses).

## 11. Measurements 2026-10-05 evening
   (discussion of further "fewer steps" levers)
- Initial trees are negligible: ctree_init_tree 14 + gtree_init_tree 14 = 0.1 s
  / 5.5k+0.4k steps (the ring-14 colouring tree unfolds to 2.6e8 nodes as a
  tree: the data is heavily DAG-shared by construction). Per-ring-size
  precomputation: no gain.
- Phase split (bytecode, fo2): kempe_tree ~90% (cf017 20.9 of 23.7 s, cf033
  6.8/8.0, cf060 22.2/24.3, cf110 contract 35 of 1462 s);
  contract_ctree/cpcolor ~5-10%.
- Early exit of the closure once the contract colourings are excluded
  (check4ct_prof.ml = instrumented OCaml checker,
  memory/check4ct_prof_20261005.log): over all 633 configs only 0.7% of the
  restriction work happens after the disjointness point (max 6% for single
  ring-14 configs): the contract colourings are the last to be removed.
  NON-RESULT. Work distribution: ring 13+14 configs (331 of 633) = 94% of all
  restriction work; productive restrictions per config 4..131 (avg 17 at ring
  13, 20 at ring 14).
- eval_compile already delegates numeral arithmetic to
  NUM_SUC_CONV/NUM_ADD_CONV; list functions cost one inference per element
  (same as LENGTH_CONV etc.): no library-duplication slack.
- Call profile of cf110 (ring 13, 1462 s bytecode, 575M steps = 2.5 us/step;
  memory/part1_profile_20261005.log): cons normalisation + bit-stack pops
  (ctr_cons 14.5, gtr_cons 12.1, ctr_cons_pop 6.1, cons_pop 5.1) = 38%;
  leaf-counter layer (ctree_leaf 5.9, ctree_leaf_child 4.8, ctr_decr3 3.5,
  cdec1-3 9.6) = 24%; restriction-list splits (ctr_split3/acc,
  gtr_split4/acc) = 12%; emptiness tests = 10%; the restrict recursions + isnil
  tests = 5%.  Average decrement per colour is ~0.5 units (leaf walks are
  short); the 'helper' steps around each real restriction step are the slack.
  Fusion plan (fo3 layer, equivalence lemmas only): pop+cons (30 clauses) ~11%,
  decrement chain cdec123 + 1-step ctree_decr ~10%, isnil/empty tests into
  constructor-case clauses ~5-7% => ~25-30% fewer steps (~1.4x); generator
  tweaks (cache head REFLs, drop redundant TRANS) ~1.1-1.2x; total ~1.6x.

## 12. Clause fusion (fo3 layer, 2026-10-05 evening):
   1.8-2.1x on mid-size configurations
part1_fo3_dev.ml, four rounds (CHANGES_part1_eval_01.md 21:00 entry): fused
constructor-case tables for the split, decrement, cons/emptiness,
union/rotation and match helpers; unary restriction height (kills two numeral
conversions ~13.5 us and a COND per node visit); boolean selectors instead of
COND for the chromogram leaves. cf033 7.58 -> 4.15 s (steps 2.57M -> ~1.1M),
cf060 24.3 -> 11.6 s (8.47M -> 3.17M steps before round 4), cf017 23.7 -> 11.6
s; heavy configs (bytecode batch): cf110 1462 -> 647 s (2.26x), cf281 2018 ->
888 s (2.27x) -- the ring-13/14 class that is 94% of the total work gains the
most. Cost model learned: time ~ sum over steps of (c0 + c1 * clause size):
fusing removes c0 per removed step but keeps the RHS content; bigger patterns
raise c1-cost (300-clause split table slower than the 39-clause one). Per-step
cost rose from 2.9 us to ~3.5 us while the step count fell 63%: the "fewer
steps" lever is now largely spent; what remains is the per-step kernel cost
(INST + TRANS + MK_COMB/REFL chains) = generator-level or kernel-level work.
Native (p1v4t_native, same configs, memory/p1v4t_timing_20261005.log):
1.54-1.63x (cf110 269.5 -> 165.0 s, cf219 361 -> 224 s, cf281 352 -> 228 s) =>
projected 8.7 h for all 633 instead of 13.86 h. The bytecode gain (2.26x) is
larger because the per-step OCaml overhead (dispatch, closures) that fusion
removes is a bigger share of bytecode time; natively the kernel term work
(vsubst/INST, allocation, GC) dominates what remains.

Measured on all 633 (16-process bytecode sweep, 2026-10-06): 130,858 s = 36.3 h
CPU vs 78.1 h for fo2 = 2.15x; slowest configuration 911 s (was 2018 s); every
result true and identical to the fo2 and native results.

## 12b. Final totals with the fo3 evaluator
   (native run completed 2026-10-06 07:28 UTC)
All 633 checks in 30,605 s = 8.50 h natively (fo2: 13.86 h => 1.63x); bytecode
sweep 36.3 h (fo2: 78.1 h => 2.15x); same theorems (REDUCIBILITY, FOUR_COLOR
hyps 0), exit 0, no fatal lines. End-to-end native wall time 10 h 9 min
including the load. Overall history: 35 days (March estimate) -> 13.5 days ->
78 h -> 36 h bytecode; 14 h -> 8.5 h native.

## 13. Native GC statistics (p1v4t_native,
   cf110 + cf219 after the 8.5-min head load; OCAMLRUNPARAM=v=0x400)
allocated 110.9 G words (~890 GB) in ~900 s = ~1 GB/s; minor collections 423k,
major 457, promoted 1.67 G words (1.5%: the minor heap absorbs almost
everything), heap 50M words (400 MB), 16 compactions. With ~6e8 evaluation
steps in the check phase this is ~150 words (~1.2 KB) allocated per step: the
instantiated clause (INST rebuilds the whole clause term), the MK_COMB/TRANS
results and the Sequent records. GC tuning (s=8M,o=200): cf110 167.2 s vs 163.2
s default = NON-RESULT natively as well (cf219 225.0 vs 222.0 s with 32x fewer
minor collections); the cost is the allocation volume itself (memory
bandwidth), not collection. perf sampling is unavailable (perf_event_paranoid =
4). Remaining native levers: fewer/smaller instantiated terms per step
(generator-level: e.g. avoid re-instantiating large RHS when only a subterm is
needed), or parallelism.

## 14. Parallel runs in one process (OCaml 5 domains, 2026-10-14)
parallel.ml (OCaml 5 or later), loaded before make.ml as make_parallel.ml
does, runs the two big computations in OCaml domains through the hooks of
par_hook.ml (plain OCaml 4.03; by default everything is sequential, as
before): parallel.ml's par_domain_map (an atomic job counter, one result
slot per job read after Domain.join, printing under a mutex) serves
part2_run.ml's p2_run_parallel (the 633 checks, heaviest first by the
measured p2_cost_order of part2_cost_order.ml) and present_eval.ml's
prove_exclude_parallel (each presentation script is run with its
Reducible/Hubcap/Similar side conditions ASSUMEd and collected; they are then
evaluated in parallel and discharged by PROVE_HYP).  Every theorem is still
made by the kernel.  The evaluations share no mutable state: the
generated evaluator calls only kernel rules, the NUM_*_CONVs and
cprsize_conv (SIMP_CONV reads the global simpset); HOL Light's
string_of_term shares one buffer (hence the mutex); compute_fast.ml enters a
constant it has not seen into the compset (assoc_clause), so the shared
the_present_compset is first saturated with all constant names.  Measured on
a 2 x 96-core Neoverse-V2 (Graviton4) machine, OCaml 5.3.0, where bytecode
is 3.9x slower than native:
- Part 2, bytecode, the 127 configurations of ring <= 11 (936.2 s
  sequentially, largest 13.4 s): 4 domains 237.5 s, 16: 62.2 s, 32: 36.1 s,
  64: 25.6 s (ring order, 256k-word minor heaps); 64 with the cost order and
  8M-word minor heaps: 20.2 s (46x).  1 domain: 936.2 s.
- Part 2, native, all 633 (about 9 h sequentially on this machine, from the
  per-job times; a job runs 17-30% slower when 128 run together):
  | domains | minor heap (words) | order | wall s | busy s (sum of jobs) |
  |  32 | 8M   | cost | 1084.3 | 34685 |
  |  64 | 256k | ring | 716.3 | 45753 |
  |  64 | 256k | cost | 668.9 | 42762 |
  |  64 | 8M   | cost | 569.5 | 36380 |
  |  96 | 8M   | ring | 449.6 | 39036 |
  | 128 | 8M   | ring | 399.6 | 40994 |
  | 128 | 8M   | cost | 319.0 | 40651 |
  | 128 | 32M  | cost | 304.0 | 38682 |
  | 180 | 8M   | cost | 310.0 | 46029 |
  From about 128 domains on, the longest jobs (cf281, cf562: 5 minutes under
  load) bound the wall time.  The runtime's 256k-word minor heap costs 17%
  natively at 64 domains (8% in bytecode): every domain allocates about
  1 GB/s, and a full minor heap stops all domains (507k minor collections in
  669 s at 64 domains), hence the 8M-word default of par_minor_heap.  With
  the ring order, the 9 ring-14 jobs that miss the first wave of 128 end the
  run (400 s); the cost order gives 319 s.
- Presentations, native, 128 domains: exclude5..11 in 193.6 s instead of
  6612 s (34x): exclude7 43.2 s (2404 s sequentially), exclude8 74.7 s
  (2378 s), exclude9 41.3 s (1398 s); the scripts themselves take 17 s.
  The largest side conditions bound each presentation: all of them take
  8460 s of CPU, 66 s on 128 domains, so pooling the side conditions of the
  seven presentations could save up to 2 minutes.
- End to end (make run-native-parallel: 128 domains, 8M-word minor heaps):
  14 min 40 s wall (twice) instead of about 11 h (Part 1 2 h 10 min, Part 2
  about 9 h), user 42178 s, max RSS 47.9 GB (sequential: about 1 GB);
  FOUR_COLOR with no hypotheses.  Still sequential: the Part 1 proofs
  (~6 min), the quiz tree (49 s) and the presentation scripts (17 s).
  In the bytecode toplevel (loadt "4CT/make_parallel.ml", 128 domains):
  47 min 31 s (presentations 784 s, Part 2 951 s), max RSS 59.5 GB.
