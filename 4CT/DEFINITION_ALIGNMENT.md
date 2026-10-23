# Definition fidelity: HOL Light 4CT package vs Gonthier's Coq proof

Date: 2026-10-08.  Scope: every definition phrase of the HOL package
(`pkg/*.ml`, 749 phrases / 865 constants, `hol_defs.txt`) against every
`Definition/Fixpoint/Inductive/Record/Let/Notation` of
`fourcolor/theories/proof/*.v` (1,165 entries, `coq_defs.txt`), starting from
the name-based alignment `defs_alignment.txt` (522 matched / 563 Coq-only /
332 HOL-only) and extending it by concept where names differ.  Read-only
audit; no file other than this one was created or modified.

## 1. Summary

### 1.1 Counts

576 Coq definitions (all of Gonthier's combinatorial layer, i.e. everything
outside the real-plane files and outside section-local `Let`s) were aligned
with a HOL definition and given a verdict:

| verdict | count |
|---|---|
| FAITHFUL | 532 |
| REFORMULATED (provably equivalent, different formulation) | 34 |
| POSSIBLE DISCREPANCY, deliberate and compensated (triad clause)
  | 0 (was 3 until round 5, 2026-10-09: `valid_contract`,
  `C_reducible`/`c_reducible`, `cfreducible` now have Coq's triad clause and
  are F) |
| POSSIBLE DISCREPANCY, benign (meaning differs only off the intended domain)
  | 5 (`connected`, `scycle`, `ucycle_plain_quasicubic`, `chordless`,
  `cpker`) |
| UNIDIOMATIC (faithful, clumsy)
  | 1 (`excluded_arity`; `qzt_truncate` was rewritten as Gonthier's one-line
  `match` in round 5, 2026-10-09) |

Two data sets were compared programmatically (section 2, cfmap/configurations
and discharge): all 633 configurations (construction programs, contract
references, list order, 63 `Config*` symmetry flags) and all 37 distinct
discharge rules (38 entries of `base_drules`) are identical to Coq's.

Of the 563 Coq-only names: 192 belong to the real-plane layer (dedekind,
realplane, grid, gridmap, matte, finitize, approx, discretize, fourcolor.v),
223 are section-local `Let`s, 14 are local `Notation`s, and 134 are
Definitions/Records/Inductives/Fixpoints that HOL inlines, represents
differently, or does not need (section 3; nothing load-bearing is missing).
Of the 332 HOL-only names, about 110 are datatype constructors that the
name-based alignment did not pair, the rest are ssreflect-library
replacements, recursion helpers, section-hypothesis bundles, fresh-dart
construction for cfmap, and the HOL-specific planar-graph and plane-map forms
(section 4).

### 1.2 Overall verdict

The combinatorial formalization is definition-for-definition faithful to
Gonthier's, modulo the expected de-ssreflectification and five global
conventions (section 5): dart guards `x IN dart H`; `ITLIST`/`ALL`/`LAST` for
right-to-left fixpoints over construction programs (orientation is the same
as Coq's: the head of a `cprog` is the LAST step applied); HOL lists for
seqs with `REVERSE`/`rot_list`/`rotr_list`/`arc_list`/`nextc` for
`rev`/`rot`/`rotr`/`arc`/`next`; a single dart type `A` for every derived
hypermap (so Coq's subtype injections `snipd`, `embd`, `icpY`, ... are
identities and `minimal_counter_example` is same-type minimality); and ONE
genuine convention change in `color.ml`: HOL's `ctrace` prepends the checksum
and HOL's `trace_col` is Coq's `urtrace = rotr 1 (trace)` (section 5.2).
The trace convention is applied consistently (every HOL ring-trace statement
carries the compensating rotation, and the Kempe-tree layer uses `ctrace_a`,
which IS Coq's `ctrace`).

### 1.3 Possible discrepancies (all explained; none affects `FOUR_COLOR`)

Deliberate and compensated:

1. RESOLVED in round 5 (2026-10-09, item E).  Until then `valid_contract`
   lacked Coq's 4th clause
   `valid_contract_triad : size cc = 4 -> ~~ [disjoint kernel r &
   triad (insertE cc)]` (coloring.v:462) and the package compensated by stating
   `reducibility` as the computational check, recovering the triad from the
   check (CHECK_REDUCIBLE_TRIAD_HYP) and threading it as an explicit hypothesis
   of NOT_EMBED_REDUCIBLE / EMBED_VALID_CONTRACT_TRIAD.  Now `valid_contract`
   (coloring.ml) has the clause
   `(LENGTH cc = 4 ==> ?x0. x0 IN kernel H r /\ triad H (insertE H cc) x0)`
   (Coq's `~~ [disjoint kernel r & triad (insertE cc)]` in existential form;
   since round 8 without the former redundant `x0 IN dart H` conjunct -- the
   kernel is dart-restricted, IN_KERNEL), `triad` lives in coloring.ml in the
   set form `2 < CARD {y | y IN face H x0 /\ fband H p (edge_map H y)} /\
   ~(!z. MEM z p ==> adj H x0 z)` (TRIAD_LIST in contract.ml is the list form;
   the two agree because the face orbit is duplicate-free), the triad-witness
   chain moved into cfcontract.ml where CONTRACT_CTREEP proves the clause, the
   side channel is deleted, and NOT_EMBED_REDUCIBLE_CONFIG follows from
   CHECK_REDUCIBLE_VALID + NOT_EMBED_REDUCIBLE as in present.v:183.
   `c_reducible` and `cfreducible` are exactly Coq's; `reducibility` is still
   stated as the check (R), unaffected.

Benign (the two sides differ only on inputs outside the intended domain, and
the HOL theorem statements carry the needed side conditions):

2. `connected` (hypermap.v:198) is `n_comp glink G == 1`, false for the empty
   hypermap; HOL `connected_hypermap` (hypermap.ml:283) is
   `!x y. x IN dart H /\ y IN dart H ==> gcomp H x y`, true for the empty map.
   HOL has `CONNECTED_NCOMP` (needs `~(dart H = {})`) and
   `NCOMP_EQ_1_CONNECTED`; `MCE_CONNECTED` (birkhoff.ml:1734) is stated with
   the HOL form.  No theorem mentioning a possibly empty map depends on this.
3. `scycle`/`ucycle` (geometry.v:210, 535): ssreflect `cycle e [::] = true`,
   so Coq's `scycle rlink [::]`, `ufcycle node [::]` and `sfcycle edge [::]`
   hold; HOL `list_cycle e p <=> ~(p = []) /\ list_path e (LAST p) p`
   (geometry.ml:698) is false on `[]`.  Affects `scycle`,
   `ucycle_plain_quasicubic`, the ring clauses of `patch`, `sew_context`,
   `embed_context`, `contract_ring`: all HOL versions require nonempty
   rings.  Every ring in the proof is nonempty (`proper_ring` needs 2+
   darts; configuration rings have `cprsize >= 2`), so nothing is lost.
4. `chordless` (geometry.v:764):
   `r \subset [pred x | [disjoint adj x & non_adj_r x]]` with
   `non_adj_r x = [predD1 [predD1 r & prev r x] & next r x]`; for `size r >= 3`
   this also forbids `adj x x`.  HOL `chordless` (geometry.ml:1052) is
   index-based, `!i j. ... adj H (EL i r) (EL j r) /\ ~(j = (i+1) MOD n) /\
   ~(i = (j+1) MOD n) ==> i = j`, and allows `adj x x`.  `adj x x` means
   `?x' IN face x. cface (edge x') x'`, i.e. a bridge, so under `bridgeless`
   the two agree.  All HOL uses (contract.ml:1014,1506;
   birkhoff.ml:2966,4252,4413) are under
   `bridgeless`/`minimal_counter_example`; the HOL version is the weaker
   hypothesis where used as a hypothesis, so the HOL theorems are at least as
   strong as Coq's.
5. `cpker` (cfmap.v:1217 vs cfmap.ml:5476): for `CpH :: cp'` Coq adds the
   SECOND element of `cpring (cpmap cp')` (and returns `[::]` if the ring has
   < 2 darts); HOL adds the pointer `SND (cpmap cp')`, which IS the second
   ring element whenever the ring has 2+ darts.  Equal on every
   `config_prog` (ring size >= 2); differ only on malformed programs, where
   `cpker` is never used.

Not discrepancies but worth knowing (details in section 5): the `ctrace`/
`trace` convention; `minimal_counter_example` quantifies over hypermaps of
the same dart type (Coq: all finite types), compensated by the
isomorphism-transfer lemmas around `hm_iso` (birkhoff.ml:3445); the semantic
`cmp_range`/`meet_range` (part.ml:322, 477) replacing Coq's lookup tables;
HOL `cprsize` is the semantic ring length while Coq's syntactic `cprsize` is
HOL's `cpringsize`; `untrace` inverts `ptrace` (one more element than Coq's).

## 2. Per-theory alignment tables (Gonthier's file order)

Verdicts: F = FAITHFUL, R = REFORMULATED, PD = POSSIBLE DISCREPANCY,
PDb = POSSIBLE DISCREPANCY (benign), U = UNIDIOMATIC.  "inl." = inlined.
Line numbers refer to the Coq `.v` and the HOL `pkg/*.ml` files.

### 2.1 hypermap.v -> hypermap.ml, jordan.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `hypermap` record (dart finType, edge/node/face, `cancel3 edge node face`)
  | `hypermap_pred` + type `hypermap`, `dart`, `edge_map`, `node_map`,
  `face_map` (hypermap.ml:46-73) | F
  | 4-tuple subtype: `FINITE (dart)`, each map `permutes dart`,
  `e o n o f = I`.  `permutes` makes maps identity off darts (so `inverse` =
  composition formula everywhere). |
| `cedge`/`cnode`/`cface` (fconnect)
  | `y IN edge H x`, `cnode`, `cface` (orbit sets `edge/node/face` =
  `orbit_map`) | F
  | HOL `edge H x` is the ORBIT (Coq `cedge x`); Coq `edge x` is HOL
  `edge_map H x`. |
| `glink` | `glink` :274 | F | |
| `connectedb`/`connected` (`n_comp glink G == 1`)
  | `connected_hypermap` :283 | PDb
  | differs on the empty map (see 1.3.2). `number_of_components` = `n_comp`. |
| `gcomp` (`connect glink`) | `gcomp` :278 | F | explicit path formulation. |
| `Euler_lhs`, `Euler_rhs`, `genus`, `planarb`/`planar`
  | `euler_lhs`, `euler_rhs`, `genus`, `planar_hypermap` :301-312 | F
  | `(lhs - rhs) DIV 2`, cutoff subtraction as in Coq. |
| `even_genus` | `even_genus` (jordan.ml:21) | F | |
| `clink` (`relU (frel (finv node)) (frel face)`)
  | `clink` :319 `x = node_map H y \/ face_map H x = y` | F
  | inverse eliminated via `node_map` bijective. |
| `Moebius_path` | `moebius_path` (jordan.ml:25) | F
  | `uniq`=`PAIRWISE (~=)`; `mem2` (jordan.ml:26) is the existential form of
  ssreflect `mem2` (equivalent); `finv node (last x p)` =
  `inverse (node_map H) (LAST q)`. |
| `Jordan` | `jordan` (jordan.ml:35) | F | |
| `permN`, `permF` | `permN`, `permF` :364-367 | F | |
| `dual` (`finv edge, finv face, finv node`)
  | `dual` :413 `(n o f, e o n, f o e)` | F
  | compositions equal the inverses by `e o n o f = I`. |
| `mirror` (`face \o node, finv node, finv face`)
  | `mirror` :451 `(f o n, f o e, e o n)` | F | |
| `eqm`, `cancel3` | - | -
  | not needed: HOL hypermaps are extensional tuples. |

### 2.2 walkup.v -> walkup.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `WalkupE` (darts `{x | x != z}`, `skip node`, `skip face`, explicit
  `skip_edge`) | `edge_walkup` :30 | R
  | darts `dart H DELETE z`; node' = `swap(z,n z) o n`, face' =
  `swap(z,f z) o f` (= `skip`); edge' = `inverse face' o inverse node'`, which
  equals Coq's `skip_edge` by `skip_edgeK`. |
| `WalkupN` = `permF (WalkupE (z : permN G))` | `node_walkup` :115 | F | |
| `WalkupF` = `permN (WalkupE (z : permF G))` | `face_walkup` :118 | F | |
| `cross_edge` (`cedge z (node z)`) | `cross_edge` :531 | F | |
| `skip`, `skip1`, `skip_edge`, `skip_edge1`, `skip_edge_domain`, `WalkupI`
  | inl. | - | subtype plumbing; `z_barb_z` Let = HOL `dart_degenerate`. |

jordan.v has no definitions; HOL `clink1`, `iterlist` are proof helpers.

### 2.3 geometry.v -> geometry.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `bridgelessb`/`bridgeless` | `bridgeless` :274 | F | |
| `loopless` | - | -
  | only used for `bridgeless_dual`; HOL's dual route (`FOUR_COLORABLE_DUAL`)
  does not need it. |
| `arity` (Notation `order face`)
  | `arity` :266 (`orbit_size (face_map H)`) | F | |
| `fband`, `kernel` | `fband` :667, `kernel` :676 | F
  | `kernel` carries `x IN dart H` (the 2026-10-04 fix; Coq's pred ranges over
  the finite dart type). |
| `fproj` (`nth (froot face x) p (find (cface x) p)`) | `fproj` :844 | R
  | first element of `p` in `face x`; default `x` instead of `froot face x`
  when `~fband p x` (both lie in `face x`; only used under `fband`). |
| `simple` (`uniq (map (froot face) p)`), `simple_rec` | `face_simple` :711
  | R / F | HOL = Coq `simple_rec`; equal to `simple` by Coq `simple_recI`. |
| `scycleb`/`scycle` (`cycle e p && simple p`)
  | `scycle` :752 (`list_cycle e p /\ face_simple H p`) | PDb
  | empty-list convention (1.3.3). `list_path`/`list_cycle` = ssreflect
  `path`/`cycle` otherwise. |
| `plainb`/`plain`, `cubicb`/`cubic`, `precubic`, `pentagonal`
  | `plain_hypermap` :287, `cubic_hypermap` :295, `precubic` :306, `pentagonal`
  :198 | F | `order` = `orbit_size`; guards `x IN dart H`. |
| `planar_bridgeless`, `plain_cubic`, `plain_cubic_connected`,
  `plain_cubic_pentagonal`, `planar_bridgeless_plain`,
  `planar_bridgeless_plain_precubic` | same names :434-454 | F
  | records -> conjunctions. |
| `planar_plain_cubic_connected`, `planar_bridgeless_plain_connected`,
  `scycle_planar_bridgeless_plain_quasicubic_connected` (+`_pbpc_base`)
  | inl. (conjunctions in `embed_context`, theorem hypotheses) | - | |
| `quasicubic` (`cubicb [predC r]`) | `quasicubic` :369 (set argument) | F | |
| `plain_quasicubic` | `plain_quasicubic` :1867 (`set_of_list r`) | F | |
| `ucycle_plain_quasicubic` (`ufcycle node r`)
  | :1871 (`list_cycle node r /\ PAIRWISE (~=) r`) | PDb
  | empty-list convention. |
| `ucycle_planar_plain_quasicubic`, `ucycle_plain_quasicubic_connected`
  | :1291, :1881 | F | |
| `rlink`, `srpath`, `srcycle`, `adj`, `insertE`
  | :142, :982, :989, :320, :684 | F | |
| `rlink_connected`
  (`exists2 p, path rlink (node (face x)) (rcons p y) & all a p`) | :1045 | F
  | HOL's path includes the endpoint (`LAST p = y`). |
| `chordless` | `chordless` :1052 | PDb | diagonal case (1.3.4). |

### 2.4 cube.v -> cube.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `cube_tag` | `cube_tag` :36 | F | |
| `cube_dart` (`cube_tag * G`)
  | `cube_D` :86 (`(:cube_tag) CROSS dart G`) | F | |
| `cube_edge`, `cube_node`, `cube_face`
  | :39, :46, :53 (+ guarded `cube_emap/nmap/fmap`) | F
  | all 18 cases identical. |
| `cube` (`locked qmap`) | `cube` :193 | F | |
| `cube_tag_enum`, `cube_tag_code`, `tsI`/`tsE` | - | - | finType machinery. |

### 2.5 color.v -> color.ml (palette in ctree.ml, count_cbit1 in initctree.ml)

| Coq | HOL | verdict | note |
|---|---|---|---|
| `color`, `palette`, `addc`, `cbit0`, `cbit1`, `ccons`, `edge_perm`, `permc`,
  `inv_eperm` | color.ml:26-192, `palette` ctree.ml:35 | F
  | tables checked entry by entry. |
| `eqc` | `=` on `color` | - | |
| `head_color`, `proper_trace`, `ptrace`, `permt`, `sumt`
  | :300, :268, :248, :261, :254 | F | |
| `ctrace et = rcons et (sumt et)` | `ctrace et = CONS (sumt et) et` :258 | R
  | checksum PREPENDED.  kempetree.ml:259 `ctrace_a et = APPEND et [sumt et]`
  is Coq's `ctrace` and is what the Kempe-tree layer uses. |
| `trace lc = ctrace (ptrace lc)`
  | `trace_col lc = ptrace (CONS (LAST lc) lc)` :277 | R
  | HOL `trace_col` = Coq `urtrace` = `rotr 1 (trace lc)` (Coq
  `urtrace_trace : urtrace (rot 1 lc) = trace lc`).  HOL lemmas
  `TRACE_COL_CTRACE_PTRACE`, `TRACE_COL_ROT1`, `TRACE_COL_REVERSE`. |
| `urtrace` | `trace_col` | F | |
| `untrace c0 et = scanl addc c0 (belast Color0 et)` (length = size et)
  | `untrace` :285 (length = size et + 1) | R
  | HOL's is the inverse of `ptrace` (`ptrace (untrace c0 et) = et`); it equals
  Coq's `untrace c0 et ++ [c0 + sumt et]`. |
| `edge_rot`, `ttail`, `even_tail`, `even_trace`, `etrace_perm`, `etrace`,
  `etail`, `eptrace` | :76, :516-540 | F | |
| `count_cbit1` | initctree.ml:21 | F | |
| `colseq` | `color list` | - | |

### 2.6 coloring.v -> coloring.ml, preembedding.ml, contract.ml,
    embed_contract.ml, cfquiz.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `coloring` (`invariant edge k =1 pred0 /\ invariant face k =1 G`)
  | `coloring` :52 | F | |
| `ring_trace`, `cc_ring_trace` | :64, :91 | R
  | use `trace_col` (= `rotr 1` of Coq's trace); compensated in every statement
  (e.g. `KEMPE_TREEP` uses `rot_list 1 (rot_list 1 (cpring ..))` where Coq has
  `rot 1 (cpring ..)`; `KEMPE_MAP` is stated for all rings `r`, so equivalent
  by `trace_rot`). |
| `four_colorable`, `graph_coloring`, `graph_four_colorable`, `cc_coloring`,
  `cc_colorable` | :58-87 | F
  | `invariant edge k =i insertE cc` =
  `k (edge x) = k x <=> MEM x (insertE cc)`. |
| `minimal_counter_example` | :218 | R
  | HOL minimality ranges over `H':(A)hypermap` of the SAME type; Coq over all
  finite types.  Sufficient: all reductions stay in type `A` or are transferred
  by `hm_iso` (birkhoff.ml:3445, `ISO_*` lemmas); `FOUR_COLOR_HYPERMAP` picks
  the minimal counterexample inside `(cube_tag#A)hypermap`. |
| `good_ring_arity` (`pred4 3 4 5 6`)
  | :228 (`3 <= arity /\ arity <= 6`) | F | |
| `at_radius2`, `radius2 (kernel r)`
  | `radius2_kernel` (cfquiz.ml:122) and the last clause of `embed_context`
  (embed.ml:44) | R
  | unfolded:
  `?x0 IN kernel. !w IN kernel. ?w1 w2. cface x0 w1 /\ cface w w2 /\
  edge w1 IN kernel /\ cface (edge w1) (edge w2)`; equivalent to
  `exists z in A, adj x0 z /\ adj w z` because the kernel is fband-closed. |
| `embeddable` record | `embed_context` (embed.ml:44) | R
  | bundles the Section Embed hypotheses: planar/plain/bridgeless/connected Gc,
  node-scycle+uniq+in-dart ring, `quasicubic`, `good_ring_arity` on the ring,
  radius-2 kernel, `minimal_counter_example Gm` (+ its consequences),
  `preembedding`, `h` into `dart Gm`.  cfquiz.ml:132 explains why `embeddable`
  is not stated separately. |
| `sparse p` (`simple (p : seq (permF G))`)
  | `sparse` :233 (`!i<j. ~cnode (EL i p) (EL j p)`) | R
  | pairwise distinct nodes. |
| `triad` | `triad` (coloring.ml, round 5) | F
  | `2 < count adjp (orbit face x)` =
  `2 < CARD {y \| y IN face H x0 /\ fband H p (edge_map H y)}` (set form; the
  list form `2 < LENGTH (FILTER ... (orbit_list face x0))` is the lemma
  TRIAD_LIST in contract.ml); `~~ (p \subset adj x)` =
  `~(!z. MEM z p ==> adj x0 z)`. |
| `valid_contract` (4 clauses)
  | `valid_contract` (coloring.ml, 4 clauses since round 5; round 8 dropped the
  redundant `x0 IN dart H`) | F | 4th clause in existential form (1.3.1). |
| `C_reducible` | `c_reducible` (embed_contract.ml) | F
  | = `valid_contract /\ (!et. cc_ring_trace cc (REVERSE r) et ==>
  kempe_coclosure (ring_trace (REVERSE r)) et)` (plain new_definition since
  round 5; the trace convention rotates both sides alike;
  `KEMPE_COCLOSURE_ROTR1` is the transfer). |
| `edge_central`, `preembedding` | preembedding.ml:111, :146 | F
  | `A \subset fclosure face edge_central` =
  `?y. edge_central y /\ cface x y`. |

### 2.7 patch.v -> patch.ml (gcomp_disk/rem -> birkhoff.ml)

| Coq | HOL | verdict | note |
|---|---|---|---|
| `patch` (10 clauses) | `patch` :34 | F
  | `sfcycle edge bGd` -> `scycle Gd (edge) bGd`; `ufcycle node bGr` ->
  `list_cycle node bGr /\ PAIRWISE`;
  `codom hr =i predU (predC codom hd) (map hd bGd)` restricted to `dart G`.
  Nonempty-ring convention. |
| `outer` (`fclosure face (codom hr)`) | inl. | - | |
| `gcomp_disk`/`gcomp_rem` (+ `gcompd_*`, `gcompr_*`)
  | `sub_hypermap` (birkhoff.ml:1181) | R
  | restriction of `H` to a gcomp-closed dart set, maps made identity
  outside. |
| `minimal_counter_example_is_*`
  | theorems `MCE_CONNECTED`, `MCE_PLAIN_CUBIC_CONNECTED`, ... | - | |

### 2.8 sew.v -> sew.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `sew_dart` (`{i : sew_tag & sew_dart_at i}`) | `sew_D` :292 on type `A+B` | R
  | `IMAGE INL (dart Gd) UNION IMAGE INR {xr IN dart Gr, ~MEM xr bGr}`. |
| `sewd`, `sewr` | :287, :289 | F
  | `hrd`/`hdr` Lets = `sew_hrd`/`sew_hdr` :46-49:
  `bGd[i] <-> (REVERSE bGr)[i]`, consistent with `patch_map_ring_r`. |
| `sew_edge`, `sew_node` | :295, :304 | F | guarded by membership. |
| `sew_face` (explicit, via `sew_face_r`)
  | `sew_face = inverse (sew_edge o sew_node)` :310 | R
  | forced by `e o n o f = I`; equals Coq's by `sew_map_subproof`. |
| `sew_map` | :313 | F | |
| `sew_tag`, `sew_tag_code/decode`, `sew_dart_at`, `sewr_r` | - | -
  | representation. |
| Section hypotheses `cycEbGd`, `cycNbGr`, `sz_bG` | `sew_context` :317 | -
  | plus dart-membership of the rings. |

### 2.9 snip.v -> snip.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `dlink`, `dconnect`, `diskN`, `diskE`, `diskF`, `diskFC` | :22-51 | F
  | `connect dlink` = `dreach` :28. |
| `snipd_edge` (`next r x` on the ring), `snipd_face`
  (`face (edge (prev r x))`) | :2266, :2275 (guarded by `diskN`) | F
  | `nextc`/`prevc` :302-306 = ssreflect `next`/`prev`. |
| `snip_disk` (darts `diskN`) | :2549 | F
  | HOL `snipd_node` :2271 is `node` restricted. |
| `snipr_node` (`prev r z`), `snipr_face` (`next r (node (face z))`)
  | :2578, :2583 | F | |
| `snip_rem` (darts `~~ diskE`) | :2827 (`redart = dart /\ ~diskE`) | F
  | HOL `snipr_edge` :2574 is `edge` restricted. |
| `snipd`, `snipr`, `snipd_ring`, `snipr_ring` | identity / `r` / `REVERSE r`
  | - | single dart type. |

### 2.10 revsnip.v -> revsnip.ml, embed_prelim.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `proper_ring`, `rev_ring` | revsnip.ml:28, :66 | F | |
| `nontrivial_ring` | :673 (`fcard_face` :845) | F
  | `diskFC` intersected with `dart H` explicitly. |
| `chord_ring x = x :: arc r (fproj r (edge x)) (fproj r x)`
  | embed_prelim.ml:2589 | F
  | `arc_list` :2322 = ssreflect `arc`;
  `rot_list`/`rotr_list`/`index_list`/`take_list`/`drop_list` =
  `rot`/`rotr`/`index`/`take`/`drop`. |
| `rev_snipd_disk`, `rev_snipr_disk`, `rev_snipd_ring`, `rev_snipr_ring`
  | `snip_disk H (rev_ring H r)` etc. inl. | - | |

### 2.11 chromogram.v -> chromogram.ml; kempe.v -> kempe.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `gram_symbol`, `bit_stack`, `stack_of_bitseq`, `sumb`
  | chromogram.ml:16, :151, :160, :229 | F | |
| `gram_balanced`, `matchg`, `cgram`, `matchpg` | :31, :45, :170, :183 | F
  | every case compared (7 `matchg` cases, 7 `matchpg` cases). |
| `Kempe_closed`, `Kempe_coclosure`
  | `kempe_closed` :68, `kempe_coclosure` :75 | F | |
| `eqgs`, `bitseq_of_stack`, `chromogram` | - | - | not needed. |
| `gram_neg_rec`, `gram_neg`, `gram_flip_rec`, `gram_flip`, `gram_rot`
  | kempe.ml:25-83 | F | `rot1`/`rotr1` :59, :700 = `rot 1`/`rotr 1`. |

`Kempe_map` (kempe.v:160) vs `KEMPE_MAP` (kempe.ml:4924): same statement
`ucycle_planar_plain_quasicubic r ==> Kempe_closed (ring_trace r)` (HOL adds
`ALL (\x. x IN dart H) r`); with HOL's trace convention the two are
equivalent because both quantify over all rings and
`trace (rot n lc) = rot n (trace lc)`.

### 2.12 ctree.v, gtree.v, dyck.v, initctree.v, initgtree.v

| Coq | HOL | verdict | note |
|---|---|---|---|
| `ctree`, `ctree_pair`, `ctree_empty`, `ctree_leaf`, `ctree_empty_node`,
  `ctree_sel`, `ctree_proper`, `ctree_sub`, `ctree_mem`, `ctree_empty_pair`,
  `ctree_pair_sub`, `ctree_leaf_of`, `ctree_cons`, `ctree_cons0..3`,
  `ctree_simple_leaf`, `ctree_cons_e`, `ctree_of_ttail`, `ctree_union`,
  `ctree_rotl`, `ctree_rotr`, `ctree_cons_rot`, `ctree_union_rotlr`,
  `ctree_rotlr`, `ctree_disjoint` (27) | ctree.ml:19-209 | F
  | the `_, _` fallthrough cases of
  `ctree_union`/`ctree_union_rotlr`/`ctree_disjoint` are expanded with
  `ctree_empty`/`ctree_leaf`/`ctree_lsub/msub/rsub`; each branch checked. |
| `eq3_CtreeEmpty` | - | - | reflection inductive. |
| `gtree`, `gtree_empty`, `gtree_mem`, `has_match`, `match_count`, `gtree_sub`,
  `gtree_empty_and`, `gtree_empty4`, `gtree_pair`, `empty_gtree_pair`,
  `gtree_pair_sub`, `sgtree_partition`, `gtree_pair_partition`,
  `gtree_cons_pairs` (14) | gtree.ml:19-179 | F
  | `gtree_mem` via `gtree_sel`/`gtree_leaf_mem` (12 leaf cases checked);
  `has_match`/`match_count` via `*_fn` with `case_bitstack`. |
| `are_4_GtreeEmpty`, `spec_ctree`, `spec_gtree` | - | - | |
| `gen_dyck`, `dyck` | dyck.ml:24, :27 | F | |
| `ctree_table_sub`, `ctree_add_dyck`, `ctree_leaf_table_from`,
  `ctree_leaf_table`, `ctree_merge_pair`, `ctree_merge_table`,
  `ctree_prune_1/2/3`, `ctree_init_tree` (10) | initctree.ml:30-102 | F
  | `ctree_leaf_table_from` restated with a toggle (`leaf_from1_fn`):
  `h=1 -> [lf,lf]`,
  `h'+2 -> [lf,lf],[E,lf] ++ from (add_dyck 2 n lf) (n+1) h'`; `iteri_ctree` =
  ssreflect `iteri`; `ctree_pairmap` = `pairmap`. |
| `init_gtree_h1`, `gtree_merge_pairs`, `gtree_merge_line`, `gtree_init_table`,
  `gtree_init_tree`, `init_gtree_spec`, `gtree_table_sub` (7)
  | initgtree.ml:25-78 | F | |

### 2.13 gtreerestrict.v -> gtreerestrict.ml;
    ctreerestrict.v -> ctreerestrict.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `gtree_restriction`, `gtr_mem`, `gtr_cons`, `gsplit` | :15-62 | F | |
| `gtr_split` (10-way case on `t2,t3,bs`)
  | `gtr_split_fn` :43 with `cons_pop` :31 | F
  | `r0' = gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 r0)`,
  `r2' = cons_pop bs t2 t3 r2`, `r3' = cons_pop bs t3 t2 r3` reproduce all 10
  Coq branches (checked). |
| `gtr_match0..3` | :69-88 | F | |
| `gtp_*` (24 pairs) | :99-122 | F | |
| `gtree_restrict` | :130 | F | `GtrNil` case first in both. |
| `ctree_restriction`, `ctr_cons`, `ctr_sub`, `csplit`, `ctree_decr`,
  `ctr_e_decr`, `cdecr`, `ctree_cons_pairs`, `sctree_partition`,
  `ctree_partition`, `ctree_restrict` | ctreerestrict.ml | F
  | `ctr_split_fn` :64 with `ctr_cons_pop` reproduces `dorec`/`addr`. |
| `ctr_decr` (15-way table over gtree leaf x bitstack with `dlf1/2/3`)
  | `ctr_decr` :264 via
  `ctr_e_decr bs t e lf = ctree_decr lf (gtree_sub t bs [e])` | R
  | semantic: decrement leaf `e` by the number of matches of `[e]`; each of the
  15 table rows checked to give the same decrements (0/1). |
| `ctree_leaf_pair` (8-way table) | :415 via `ctree_if_e` | R
  | first component `ctree_cons lf1' lf2' lf3'`, second
  `ctree_cons (if lf_i' empty then lf_i else Empty)`; identical to the table. |

### 2.14 kempetree.v -> kempetree.ml, kempetree_wrap.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `ctree_size` | :20 | F | |
| `ktc_step`
  | `ktc_step h ktc0 ctu gtr gtu` :525, `ktc_stepp` :537 (pair form) | F
  | section variable `h` explicit; the closure approximation is named
  `ktc0`, as in Gonthier's header (his argument is called `closure`). |
| `ktc_step2c`, `ktc_dostep2c` | inl. in `kempe_tree_closure_fn` :543 | R
  | `step (step (ktc0 ctu ctr gtu))`. |
| `Kempe_tree_closure` | `kempe_tree_closure` :551 | F | |
| `Kempe_valid` | `kempe_valid` :556 | F
  | uses `ctrace_a` (= Coq `ctrace`), `even_fun` unfolded. |
| `Kempe_complete` | `kempe_complete` :570 | F | |
| `Kempe_tree` (`cprsize cp = h.+2`) | `kempe_tree` (kempetree_wrap.ml:152) | F
  | `2 <= cprsize`, `h = cprsize - 2`. |

### 2.15 cfmap.v -> cfmap.ml (and cfcontract.ml for masks)

| Coq | HOL | verdict | note |
|---|---|---|---|
| `cpstep` | `cpstep` :41 (`CpR'` = `CpRr`) | F | |
| `cubic_prog` (fixpoint) | `cubic_prog = ALL cubic_step` :57 | F | |
| `config_prog` (fixpoint, ends in `[:: CpY]`)
  | `~(cp = []) /\ LAST cp = CpY /\ ALL config_step cp` :72 | F | |
| `config` record (`cfsym`, `cfcontract_ref`, `cfprog`)
  | pair `(cpstep)list # (num)list` + `the_configs_sym` | R
  | `cfprog = FST`, `cfcontract_ref = SND` (cfcontract.ml:792-793). |
| `pointed_map` | `hypermap # num` | R | |
| `cpring = rev (orbit node (node (node x0)))` | :977 | F
  | `orbit_list` :958 = `orbit`. |
| `proper_cpring`, `long_cpring` | :981, :259 | F | |
| `ecpR n` (pointer `iter (order node x0 - n) node x0`)
  | `ecpR` :646 (= H), `ecpR_pt` :648 | F | |
| `ecpR'` | `ecpRr`, `ecpRr_pt` :660 | F | |
| `ecpA_edge/node/face`, `ecpA` (pointer `face (edge (face (edge x0)))` in the
  new map) | :697-882 | F | guarded by `x IN dart H`. |
| `ecp_edge`, `ecpU_node`, `ecpU_face`, `ecpU` (pointer `IcpX`)
  | `ecpU_edge` :167, :164, :179, `ecpU` :338 (`ecpU_pt`) | F
  | `IcpX`/`IcpXe` = two fresh `num`s `new_dart2 (dart H)`; all 9 cases
  checked. |
| `ecpN_node`, `ecpN_face`, `ecpN` | :384, :277, :567 | F | 8 cases checked. |
| `ecpK = ecpR 1 (ecpN ecpR')`, `ecpY = ecpN (ecpU x0)`, `ecpH = ecpN ecpY`
  | :671, :597, :601 | F | |
| `cpmap0` (bool, `negb, negb, id`, pointer `true`)
  | `cpmap0 = ({0,1}, swap(0,1), swap(0,1), I)`, pointer 1 :131 | F | |
| `cpmap` (fixpoint, head = last step)
  | `cpmap cp = ITLIST cpstep_apply cp (cpmap0,1)` :932 | F
  | same orientation: `ITLIST` applies the LAST element first. |
| `cfmap`, `cfring = rev (cpring (cfmap cf))` | cfcontract.ml:794, :795 | F | |
| `cpker` | :5476 | PDb | pointer vs 2nd ring element (1.3.5). |
| `injcp` (dependent injection) | `injcp_ctx` (cfquiz.ml:1491) | R
  | identity on old darts + context predicate. |
| `cprsize` (syntactic), `sub2ifgt2` | `cpringsize` :2069 | F
  | HOL's `cprsize` :984 is `LENGTH (cpring ..)` (the semantic size; equal by
  Coq `size_cpring`).  Naming swap, see 5.6. |
| `cpksize` | :5484 | F | |
| `cfmask`, `proper_cpmask`, `cpmask`, `cfmask1`, `cpadj`
  | cfcontract.ml:8072-8154 | F (`cfmask` R)
  | pair of bool lists; `cpadj` identical on well-formed masks (Coq returns
  `cm` on pattern failure, HOL unspecified `HD []`). |
| `cprog`, `H`, `Y`, `U`, `cons_cp`, `parse_config`, `ecp_dart`,
  `ecp_encode/decode/eq/eqMixin`, `ecpU_map`, `ecpN_map`, `ecpA_map`, `icp*`
  | - | - | syntax / finType / identity injections. |

configurations.v -> configurations.ml: `cf001..cf633`, `the_configs`,
`Config*` flags -> `the_configs_sym`: compared programmatically (parse of
`Config[*] n1 .. H .. Y` through `parse_config` semantics vs the HOL pairs):
633/633 programs and contract-reference lists identical, same order, 63/63
symmetry flags identical.  F.

### 2.16 cfcolor.v -> cfcolor.ml, cpcolor_correct.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `cfcbr2`, `ctree_cons_perm`, `cfcbr1`, `cpbranch`, `cpcolor1`, `cpcolor0`,
  `cpcolor` | cfcolor.ml:34-116 | F
  | all 7 `cpcolor1` cases and the `cpcolor0` dispatch checked;
  `foldr cpcolor1 cpbranch` = `ITLIST cpcolor1 cp' cpbranch`. |
| `cp_ht0`, `cp_tr0`, `cp_extcol` | inl., cpcolor_correct.ml:876, :912 | F
  | `ftrace lc = trace_col (rot_list 1 lc)` :188 is exactly Coq's `trace` (by
  `urtrace_trace`); `k0 \o injcp =1 k` ->
  `!x IN dart (cpmap cp2). k0 x = k x`. |
| `cpexpand1`, `cpexpand`, `pmap_eqdep` | - | -
  | Coq proof devices; HOL proves per-step extension lemmas (`kuU`, `kuY`,
  `kuH`). |

### 2.17 cfcontract.v -> cfcontract.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `ctrmsize`, `ctrmask_rec`, `ctrmask`, `ctrenum`, `nsp` | :26-150 | F | |
| `cfctr` (option)
  | `cfctr = if cfctr_ok then SOME (cfctr_map ..) else NONE` :206 | F
  | all 4 clause shapes and the `None` fall-throughs checked. |
| `ctrband`, `cfcontract_mask`, `cfcontract`, `cptriad`, `valid_ctrm`,
  `contract_ctree` | :9437-15519 | F | `mask` = `mask_list` :289. |

### 2.18 cfreducible.v -> cfreducible.ml, four_color.ml, present.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `check_reducible =
  oapp (ctree_disjoint (Kempe_tree (cfprog cf))) false (contract_ctree cf)`
  | :54 | F | |
| `cfreducible = C_reducible (cfring cf) (cfcontract cf)` | :67 | F
  | exactly Coq's since round 5 (1.3.1). |
| `reducible_in_range`, `reducibility` (present.v:73)
  | `reducibility <=> !cf. MEM cf the_configs ==> check_reducible cf`
  (four_color.ml:42) = `check_reducibility` (present.ml:197) | R
  | stronger (the check itself); `REDUCIBILITY_IMP_CFREDUCIBLE` gives Coq's
  form. |
| `cf000` | - | - | `nth` default. |

### 2.19 birkhoff.v -> birkhoff.ml; contract.v -> contract.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `cpcard`, `Birkhoff_check1`, `ctree_pick_rev_rec`, `ctree_pick_rev`,
  `do_Birkhoff_check2`, `Birkhoff_check2`, `Birkhoff_check`
  | birkhoff.ml:1699-1919 | F
  | section variables `h`, `m`, `check_basis` explicit; `Birkhoff_check`
  inductive -> `?niter cps`. |
| `spoke`, `spoke_ring = map spoke (rev (orbit face x))` | :6388, :6415 | F | |
| `adj01` | inl. | - | |
| `contract_ring` | contract.ml:20 | F
  | `{subset behead r <= insertE cc}` =
  `!x. MEM x (TL r) ==> MEM x (insertE cc)`. |

### 2.20 embed.v -> embed.ml, embed_prelim.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `pre_hom_ring` | embed_prelim.ml:2242 | F | `ac` = `kernel Gc rc`. |
| `embed` | embed.ml:1793 | F | |
| `embd_edge`, `embd_face`, `embed_disk` (darts `bc = [predC rc]`)
  | `embd_emap`, `embd_fmap`, `embed_disk` :2698-2948 | F | |
| `embd_ring = preim_seq embd erc` (`erc = map edge rc`)
  | `MAP (edge_map Gc) rc` inl. | F | |
| `embr_node`, `embr_face` (`oapp .. (pick (bGd_proj ..))`)
  | `embr_nmap`, `embr_fmap` :3387, :3396 | F | `pick` -> Hilbert choice. |
| `rdom' = image embdd [predC embd_ring]`, `embed_rem` (darts `~~ rdom'`)
  | `rdom'` :3377, `embr_D`, `embed_rem` :3935 | F | |
| `embr_ring = preim_seq embr (rev (map embdd embd_ring))` | :3967 | F | |
| `embed_cotrace = ring_trace (rotr 1 embr_ring)`
  | inl. in `NOT_EMBED_REDUCIBLE` (`rotr1 (embr_ring ..)`) | F | |

### 2.21 quiz.v, quiztree.v, cfquiz.v

| Coq | HOL | verdict | note |
|---|---|---|---|
| `qarity`, `nat_of_qarity`, `qarity_of_nat`, `question`, `isQaskR`, `flatq`,
  `flipq`, `qstepL`, `qstepR`, `quiz`, `isQuizR`, `flatqz`, `walkq`, `fitq`,
  `walkqz`, `fitqz` | quiz.ml:20-97 | F | |
| `flipqz` | :76 | R | via accessors `qra`/`qrb`. |
| `valid_quiz`, `embedqz` | :368, :376 | F
  | `simple s0c` -> `face_simple`; `fband s0c =i ac` ->
  `!x. fband .. x <=> kernel .. x`; `find`/`nth`/`findex` ->
  `findp`/`nthd`/`findex` (`minimal n. ITER n f x = y`). |
| `quiz_tree`, `qzt_proper`, `qzt_put1`, `qzt_put3`, `qzt_put3rot`, `qzt_put`,
  `qzt_empty`, `normq`, `store_cf_qz`, `cfquiz_tree`, `qzt_size`,
  `qzt_get1/2/3`, `qzt_fita`, `qzt_fitl`, `qzt_fit` | quiztree.ml | F
  | `=a` notation -> `nat_of_qarity (qarity_of_nat (arity x)) = arity x`. |
| `store_qz` | `store_qz_aux` :98 | R
  | the `normq` match via `isQaskLR`/`qLR_l`/`qLR_r`. |
| `cfquiz_tree_rec` (over `seq config`) | :119 over `((cf,sym)) list` | R | |
| `qzt_truncate` | :176 | F
  | ROUND 5 (2026-10-09): now
  `match t with QztHubNode (QztNode t5 t6 t7 t8) t9 t10 t11 ->
  QztNode t5 t6 t7 t8 \| t -> t`, Gonthier's
  `if t is QztHubNode (QztNode _ _ _ _ as t58) _ _ _ then t58 else t` verbatim
  (was an if-chain with an existential `QztNode` test, flagged U). |
| `cf_main_arity`, `cf_qzt_size1`, `cf_qzt_size`, `configs_compiled` | - | -
  | Coq sanity check that every config was stored; in HOL a lost config would
  make the unavoidability proof fail, not succeed. |
| `ring_question` record | `bool # num # question` | R | |
| `small_qarity`, `bad_small_arity`, `large_qarity`, `bad_ring_arity`, `rqs_Y`,
  `cfquiz_Y`, `rqs_H`, `cfquiz_H`, `cfquiz_rec`, `rqs_fit`, `rqs_walk`,
  `rqs_proper`, `cpradius2`, `cfquiz`, `noquiz` | cfquiz.ml:31-172 | F
  | `h`/`codom h` of Coq's injection become identity/`dart G`. |

### 2.22 part.v -> part.ml, part_mirror.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `prange`, `part`, `subpart_loc`, `pcons_s`, `pcons_`, `mem_range`,
  `part_rel`, `apply_part_rel`, `notPsubset`, `meet_prel`
  | part.ml:42-319, :397-398 | F | |
| `cmp_range` (225-entry table)
  | `cmp_range` :322 (semantic: `Psubset` if
  `mem_range r1 SUBSET mem_range r2`, `Pdisjoint` if disjoint, else
  `Pstraddle`) | R
  | Coq's `mem_cmp_range` certifies the table against the same semantics;
  spot-checked rows agree. |
| `meet_range` (table) | :477 via `rlo`/`rhi`/`rbounded`/`prange_of_bounds` | R
  | interval intersection; agrees with the table whenever the ranges meet (Coq
  `mem_meet_range`); values on empty intersections are don't-care on both
  sides. |
| `size_part`, `drop_part`, `take_part`, `cat_part`, `rot_part`, `catrev_part`,
  `rev_part`, `get_spoke`, `next_hat`, `get_hat`, `get_fan1r/2r/3r/1l/2l/3l`,
  `mirror_part_rec`, `mirror_part` | :67-272 | F | |
| `conv_part12/3/4/5`, `converse_part`
  | part_mirror.ml:368-423 (aux `cp12_aux*`, `cp3_*`, `cp4_aux`) | F
  | nested patterns split into recursive aux functions; all branches checked. |
| `prange_lo`, `prange_hi`, `good_rsplit`, `split_range`, `good_split`,
  `split_part` | :698-786 (`gsplit_*`, `ssplit_*`) | F | |
| `cmp_part`, `meet_part` | :332, :492 | F
  | `Pnil,_ => Psubset; _,Pnil => Pstraddle; _,_ => Pdisjoint` reproduced. |
| `subpart_loc_move`, `fitp`, `exact_fitp`, `tight_fitp`, `part_update`,
  `inv_face2`, `fitc` | :136-864, part_mirror.ml:340-342 | F | |
| `Part`, `s`, `h`, `f1`, `f2`, `f3` | - | - | syntax module. |

### 2.23 redpart.v -> redpart.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `zpart_loc`, `zpart`, `zproper`, `zvalid`, `zpvalid`, `zmove`, `zorg`,
  `zporg`, `zdart`, `zpfit`, `hub_range`, `zrange`, `shift_part` | :21-95 | F
  | section variables (`p0r`, `x0`, `ahub`, `G`) explicit. |
| `zshiftl`, `zshiftr` (with `p0ll = drop_part 1 p0l`,
  `p0lr = shift_part p0l p0r`, `p0rl`, `p0rr`) | :99-124 | F | |
| `zfanL/R`, `zfanLt/Rt`, `zstepL/R/Lt/Rt` | :127-236 | F
  | all 15 locations per step function checked. |
| `topqa`, `popqa`, `zpfit_top` | :240-256 | F | |
| `fitqa` (table) | `nat_of_qarity qa <= 8 /\ qa = topqa r` :247 | R
  | identical truth table. |
| `red_pcons`, `red_popr_spoke`, `red_popr_hat`,
  `red_popl_spoke/hat/fan1l/2l/3l/1r/2r/3r`, `red_pop` | :264-358 | F
  | `red_rec`, `nhub`, `p0r` explicit. |
| `fitqzp`, `red_popqzp`, `red_qzt_leaf`, `qzt_getr` | :362-416 | F | |
| `red_zpart_rec` (one 70-line fixpoint)
  | `red_zpart_rec` :489 = `red_zpart_step` :472 + `red_zpart_cases` :428 | F
  | all 1+1+1+2+3+4 `red_qzt_leaf` calls and their pop conjuncts checked
  against Coq. |
| `red_zpart`, `redpart` | :495, :506 (`redpart_loop`) | F
  | `nhub * 12` bound, `nhub = ahub` test. |

### 2.24 discharge.v -> discharge.ml; hubcap.v -> hubcap.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `drule1..drule32`, `drule2'`, `drule3'`, `drule4'`, `drule10'`, `drule31'`
  (37) | `drule1..32`, `drule2_P`.. :41-77 | F
  | Coq `Part $ .. $` notation decoded (`$ s` = `Pcons s Pr59`, `$[h] s` =
  `Pcons s h`, `$[h f1] 6` = `Pcons6`, ...) and compared programmatically:
  37/37 identical. |
| `base_drules` (38 entries, `drule1` twice) | :80 | F | same order. |
| `symmetrize_drules`, `the_drules`, `dscore1`, `dscore2`, `dscore` | :93-114
  | F | `\sum_(y in cface x)` -> `isum (face H x)`. |
| `pick_source_drules`, `pick_target_drules`, `sort_drules_rec`, `sort_drules`,
  `drule_fork_values`, `dbound1`, `dbound2`, `dboundK` | :127-165 | F
  | `nhub` explicit. |
| `sort_drules_result`, `drule_fork` records
  | pairs (`the_drule_fork` :155) | R | |
| `sort_drules_spec` | - | - | reflection inductive. |
| `hubcap`, `check_dbound1_rec`, `check_dbound1`, `check_unfit`,
  `check_dbound2_rec`, `check_dbound2`, `check_2dbound2_rec`, `check_2dbound2`,
  `tally_hubcap`, `hubcap_cover_rec`, `hubcap_cover`, `hubcap_rot`, `hub_subn`,
  `hubcap_fit` (14) | hubcap.ml:20-142 | F
  | `Posz nt` tests -> `v < &0 .. num_of_int v`; `incr_nth`/`nth 0` ->
  `incr_nth`/`nth0`; `b' *+ (n_i == 1).+1` ->
  `b' * (if n_i = 1 then &2 else &1)`. |

### 2.25 present.v / combinatorial4ct.v -> present.ml, four_color.ml

| Coq | HOL | verdict | note |
|---|---|---|---|
| `reducibility` | `reducibility`, `check_reducibility` | R | see 2.18. |
| `valid_hub` | present.ml:204 | F | plus `x IN dart G`. |
| `excluded_arity` | :207 | U
  | faithful, but carries a dummy argument `u:A->bool` only to fix the type
  variable. |
| `successful`, `forced_part`, `succeeds_in` | :211-218 | F | |

## 3. Coq-only names (563), grouped

1. Real-plane layer (192): dedekind.v 33, realplane.v 27, grid.v 38,
   gridmap.v 26, matte.v 35, finitize.v 17, approx.v 22, discretize.v 9,
   fourcolor.v 1.  HOL proves the plane form (`FOUR_COLOR_MAP`,
   map_defs/map_grid/map_main/four_color_map) by a different route over
   `real^2` (grid-minor `ADJACENCY_GRAPH_PLANAR` + compactness), so none of
   Gonthier's discrete-geometry notions (`grect`, `matte`, `gchop`,
   `refine_matte`, `approx`, ...) is needed.  (realplane.ml in the dev tree
   defines Gonthier's notions but is not part of the shipped chain.)
2. Section-local `Let`s (223) and local `Notation`s (14): abbreviations of
   section hypotheses (`planarG`, `plainGc`, `ee`, `nnn`, `ac`, `bc`, `erc`,
   `hc`, `ix`, `r1`, ...) and local lemmas stated with `Let` (`EbGdE`,
   `z_comp_preimage`, `fcard_skip_edge`, `Euler_lhs_WalkupE`, ...).  HOL has
   no sections; they become hypotheses of theorems or named lemmas.  The
   few Lets that are real definitions are matched above (`nsp`, `noquiz`,
   `hdr`/`hrd` = `sew_hdr`/`sew_hrd`, `z_barb_z` = `dart_degenerate`,
   `rdom'`, `bGd_proj` inlined, `sumb`, `p0ll..p0rr`, `nhub`, `ktc_fun`).
3. Boolean duplicates and reflection devices (13): `bridgelessb`,
   `connectedb`, `planarb`, `plainb`, `cubicb`, `scycleb`, `eqc`, `eqgs`,
   `ecp_eq`, `ecp_eqMixin`, `eq3_CtreeEmpty`, `are_4_GtreeEmpty`,
   `pmap_eqdep`, `sort_drules_spec`.
4. Type abbreviations and representation machinery (24): `cprog`, `colseq`,
   `chromogram`, `spec_ctree`, `spec_gtree`, `ctree_table`, `gtree_table`,
   `drules`; `ecp_dart`, `ecp_encode`, `ecp_decode`, `ecpU_map`, `ecpN_map`,
   `ecpA_map`; `cube_dart`, `cube_tag_enum`, `cube_tag_code`; `sew_tag`,
   `sew_tag_code`, `sew_tag_decode`, `sew_dart_at`, `sew_dart`, `sewr_r`;
   records `config`, `pointed_map`, `cfmask`, `ring_question`,
   `sort_drules_result`, `drule_fork` (pairs/lists in HOL).
5. Syntax modules (12): `Part`, `s`, `h`, `f1`, `f2`, `f3` (part.v), `H`,
   `Y`, `U`, `cons_cp`, `parse_config` (cfmap.v), `cf000`.
6. Subtype injections and dependent coercions, identities in HOL (31):
   `WalkupI`, `snipd`, `snipr`, `snipd_ring`, `snipr_ring`, `embd`, `embdd`,
   `embr`, `embd_ring`, `gcompd`, `gcompr`, `gcompd_dart`, `gcompr_dart`,
   `gcompd_edge/node/face`, `gcompr_edge/node/face`, `icpR`, `icpR'`,
   `icpU`, `icpN`, `icpK`, `icpY`, `icpH`, `icpA`, `injcp` (-> `injcp_ctx`),
   `rev_snipd_disk`, `rev_snipr_disk`, `rev_snipd_ring`, `rev_snipr_ring`.
7. Intermediate helpers inlined or replaced by an equivalent (22): `skip`,
   `skip1`, `skip_edge`, `skip_edge1`, `skip_edge_domain`, `outer`,
   `sub2ifgt2`, `cp_ht0`, `ktc_step2c`, `ktc_dostep2c`, `embed_cotrace`,
   `adj01`, `sew_face_r`, `embd_edge`/`embd_face`/`embr_node`/`embr_face`
   (renamed `*_emap/fmap/nmap`), `simple` (-> `face_simple` = `simple_rec`),
   `trace`/`urtrace` (-> `trace_col`), `at_radius2`/`radius2`
   (-> `radius2_kernel`), `embeddable` (-> `embed_context`),
   `reducible_in_range` (-> `reducibility`), `WalkupE/N/F` (renamed
   `edge/node/face_walkup`), `connected`/`planar`/`plain`/`cubic` (renamed),
   `planar_plain_cubic_connected`, `planar_bridgeless_plain_connected`,
   `scycle_planar_bridgeless_plain_quasicubic_connected` (+`_pbpc_base`)
   (conjunctions), `minimal_counter_example_is_*` (theorems).
8. Genuinely absent, nothing lost: `loopless` (only for `bridgeless_dual`),
   `eqm` (hypermap extensional equality; HOL hypermaps are extensional),
   `bitseq_of_stack` (proof device), `cpexpand`/`cpexpand1` (Coq's proof
   route for `cpcolor`; HOL proves `cpcolor` correct step by step),
   `cf_main_arity`/`cf_qzt_size1`/`cf_qzt_size`/`configs_compiled` (size
   sanity check of the quiz tree).

## 4. HOL-only names (332), grouped

1. Datatype constructors counted as "constants" by the name alignment
   (about 110): `Color0..3`, `Eperm*` (6), `Gpush/Gskip/Gpop0/Gpop1`,
   `Bstack0/Bpush0/Bpush1`, `CtreeNode` (and `CtreeEmpty`, `CtreeLeaf`,
   `CtreePair`, `GtreeEmpty`, `GtreePair`, `CtrCons`, `GtrCons`, `Zpart`,
   `Pcons`, which the alignment paired with Coq's SAME-NAMED Boolean tests
   or smart constructors `ctree_empty`, `ctree_leaf`, `ctree_pair`,
   `gtree_empty`, `gtree_pair`, `ctr_cons`, `gtr_cons`, `zpart`, `pcons_`:
   these pairings are artifacts; HOL has the real counterparts
   `ctree_empty`, `ctree_leaf`, `gtree_empty`, `ctr_cons`, `gtr_cons`,
   `pcons_` too), `GtreeLeaf*` (8), `GtreeNode`, `GtrNil`, `CtrNil`,
   `CpR/CpRr/CpY/CpH/CpU/CpK/CpA`, `CT*` (6), `Pr*` (15), `Pnil`,
   `Pcons6/7/8`, `Pspoke/Phat/Pfan1/2/3`, `Pdisjoint/Pstraddle/Psubset`,
   `Qa5..Qa11`, `Qask*` (7), `QztNil/QztLeaf/QztNode/QztHubNode`, `Z*` (15),
   `Hubcap0/1/2`.  Note also `embdd` (Coq composite injection) was paired
   with `embd_D` (HOL dart set): an artifact.
2. Hypermap representation: `hypermap_pred`, `tuple_hypermap`, `dart`,
   `edge_map`, `node_map`, `face_map`, `mk_hypermap`, `edge`, `node`, `face`
   (orbits), `orbit_map`, `orbit_size` (= `order`), `set_of_orbits`,
   `edge_set`, `node_set`, `face_set`, `number_of_edges/nodes/faces`
   (= `fcard`), `component`, `set_of_components`, `number_of_components`
   (= `n_comp`), `fclosed`, `fcard_face`, `sub_hypermap`, `hm_iso`.
3. ssreflect-library replacements: `list_path`, `list_cycle`,
   `face_simple`, `nextl`, `nextc`, `prevc`, `INDEXL`, `index_list`,
   `take_list`, `drop_list`, `rot_list`, `rotr_list`, `rot1`, `rotr1`,
   `arc_list`, `rotate_to`, `uniq_list`, `mask_list`, `incr_nth`, `nth0`,
   `iterlist`, `orbit_list`, `list_find`, `findex`, `findp`, `nthd`,
   `palette` (Coq notation), `case_bitstack`, `mem2`, `iteri_ctree`,
   `ctree_pairmap`, `catrev_cp`.
4. Fresh-dart construction for cfmap (no sum types): `new_dart`,
   `new_dart2`, `ecpU_edge`, `ecpU_pt`, `ecpN_pt`, `ecpY_pt`, `ecpH_pt`,
   `ecpR_pt`, `ecpRr`, `ecpRr_pt`, `ecpK_pt`, `ecpA_pt`, `cpstep_apply`,
   `cubic_step`, `config_step`, `cpringsize` (= Coq `cprsize`).
5. Recursion-scheme helpers (HOL `define`/`new_recursive_definition` need
   one structural argument; nested patterns split into aux functions):
   `has_match_fn`, `match_count_fn`, `gen_dyck_fn`, `ctree_add_dyck_fn`,
   `leaf_from1_fn`, `gtree_merge_line_fn`, `gtree_init_table_fn`,
   `gtr_split_fn`, `ctr_split_fn`, `ctree_restrict_fn`,
   `kempe_tree_closure_fn`, `ktc_stepp`, `cfctr_ok`, `cfctr_map`,
   `zshiftl_aux`, `zshiftr_aux`, `zstepL/R/Lt/Rt_loc`, `zrange_loc`,
   `red_pop_loc`, `red_zpart_cases`, `red_zpart_step`, `redpart_loop`,
   `cp12_auxA/B/C`, `cp3_1/2/3`, `cp4_aux`, `gsplit_*`, `ssplit_*`,
   `store_qz_aux`, `isQaskLR`, `qLR_l`, `qLR_r`, `qra`, `qrb`, `isQaskL`,
   `isCpR`, `cpr_arg`, `case_ctree_node`, `case_gtree_node`, `cons_pop`,
   `ctr_cons_pop`, `gtr_isnil`, `ctr_isnil`, `isQztHubNode`,
   `ctree_lsub/msub/rsub`, `ctree_leaf_child`, `ctree_if_e`, `gtree_isleaf`,
   `gtree_sel`, `gtree_leaf_mem`, `mask_pred1`, `mask_pred1_from`,
   `cptriad_cond`, `sym_drule`, `the_drule_fork`, `rlo`, `rhi`, `rbounded`,
   `prange_of_bounds`, `zp_zi`, `zp_pl`, `zp_pr`.
6. Section-hypothesis bundles and restricted maps (Coq Variables /
   Hypotheses / Lets): `embed_context`, `sew_context`, `redpart_hyps`,
   `injcp_ctx`, `dart_degenerate`, `clink1`, `rclink`, `redart`, `dreach`,
   `snipd_node`, `snipr_edge`, `embd_D/nmap/emap/fmap`,
   `embr_D/emap/nmap/fmap`, `cube_D/emap/nmap/fmap`, `sew_D`, `sew_hdr`,
   `sew_hrd`, `walk_Y`, `walk_H` (induction invariants), `kuU`, `kuY`,
   `kuH`, `kcfY`, `kcfH`, `kcfK` (extension colourings), `ftrace`,
   `ctrace_a`, `trace_col`, `dscoreF`, `hcw`, `hcwsum`, `contract_walkup`,
   `radius2_kernel`, `check_reducibility`, `the_quiz_tree`, `valid_hub`
   companions.
7. HOL-specific final forms: `graph_hypermap`, `proper_coloring`,
   `color_num` (planar_graph_link.ml); `plane_map`, `adjacent_regions`,
   `map_colorable`, `planar_graphs_four_colorable`, `adjacency_graph`
   (map_defs.ml); `grid_vertices`, `grid_edges`, `grid_point`, `grid_near`,
   `grid_lpath`, `edge_other` (map_grid.ml).  `plane_map`,
   `adjacent_regions` and `map_colorable` are realplane.v's `simple_map`,
   `adjacent` and `colorable_with`, reformulated with a map given as a set
   of regions instead of a partial equivalence relation on points (a
   border point in no third closure is Coq's not-corner condition).
8. Parallel definitions that duplicate a Coq notion under another name
   (harmless, but candidates for consolidation): `ctrace` (prepend) vs
   `ctrace_a` (= Coq `ctrace`); `check_reducibility` = `reducibility`;
   `radius2_kernel` duplicates the last clause of `embed_context`;
   `cprsize` (semantic) vs `cpringsize` (= Coq `cprsize`); `drule_fork_values`
   vs `the_drule_fork`; `trace_col` named unlike Coq's `urtrace`.

## 5. Conventions

### 5.1 Dart guards, partiality, inverses
- Coq's finite dart type becomes `dart H : A->bool`; every HOL definition
  that quantifies over darts guards with `x IN dart H` (`bridgeless`,
  `plain_hypermap`, `coloring`, `kernel`, `snip*`, `ecp*`, `embd_*`,
  `embr_*`, `cube_*`, `sew_*`).  Derived maps are made the identity off
  their dart set, so `permutes` holds and `inverse` is a true two-sided
  inverse on all of `A` (`edge_walkup`, `sew_face`, `clink`, `dconnect`,
  `moebius_path` use `inverse` of `node_map`/`face_map` legitimately).
- `HD []`, `TL []`, `EL i []`, `LAST []`, `@x. ...` appear only in
  well-formedness-guarded positions (`cpadj`, `ctrband`, `cfquiz_rec`,
  `cfctr_*` on proper masks/programs; `fproj`, `embedqz` under `fband`).
  Where Coq returns an explicit default (`cm`, `Cfmask [::] [::]`), HOL
  returns an unspecified value; no theorem depends on these inputs.
- `set_of_orbits`/`fcard_face` over predicates that may contain non-darts
  are intersected with `dart H` where it matters (`nontrivial_ring`).

### 5.2 Traces: the one real convention change
- Coq: `ptrace lc = pairmap addc c lc'`, `ctrace et = rcons et (sumt et)`,
  `trace lc = ctrace (ptrace lc)`,
  `urtrace lc = pairmap addc (last Color0 lc) lc`, with
  `urtrace (rot 1 lc) = trace lc`, `trace (rot n lc) = rot n (trace lc)`,
  `trace (rev lc) = rot 1 (rev (trace lc))`.
- HOL: `ptrace` as Coq; `ctrace et = CONS (sumt et) et` (checksum FIRST);
  `trace_col lc = ptrace (CONS (LAST lc) lc)` = Coq `urtrace lc` =
  `rotr 1 (Coq trace lc)`; `TRACE_COL_CTRACE_PTRACE` relates them.  The
  Kempe-tree layer (kempetree.ml, kempetree_wrap.ml, birkhoff.ml) uses
  `ctrace_a et = APPEND et [sumt et]`, i.e. Coq's `ctrace`, so `kempe_valid`
  and `kempe_complete` are literally Coq's.  cpcolor_correct.ml uses
  `ftrace lc = trace_col (rot_list 1 lc)` = Coq's `trace` exactly.
- Consequences, all handled consistently: `ring_trace`/`cc_ring_trace`
  are the `rotr 1` images of Coq's; `KEMPE_TREEP` is stated with
  `rot_list 1 (rot_list 1 (cpring ..))` where Coq has `rot 1 (cpring ..)`;
  `KEMPE_MAP` and `c_reducible` are equivalent to Coq's because the
  Kempe closure/coclosure notions are rotation-invariant
  (`KEMPE_COCLOSURE_ROTR1`, `RING_TRACE_ROT1_RING_EQ`, Coq
  `match_gram_rot`).  `untrace` is the inverse of `ptrace` (one element
  longer than Coq's).

### 5.3 Lists, rings and programs: orientation
- Coq `seq` -> HOL `list`; `rcons l x` -> `APPEND l [x]`; `rev` -> `REVERSE`;
  `rot n`/`rotr n` -> `rot_list n`/`rotr_list n` (and `rot1`/`rotr1`);
  `next`/`prev` -> `nextc`/`prevc`; `arc` -> `arc_list`; `index` ->
  `index_list`/`INDEXL`; `mask` -> `mask_list`; `belast e et` ->
  `BUTLAST (CONS e et)`; `nth x0 s i` -> `nthd x0 s i` / `EL`.
- Rings: `cpring = REVERSE (orbit_list node (node (node x0)))` and
  `cfring = REVERSE cpring` exactly as Coq (`rev (orbit ..)`,
  `rev (cpring ..)`); `rev_ring = REVERSE (MAP edge r)`;
  `spoke_ring = MAP spoke (REVERSE (orbit_list face x))`;
  `embr_ring = REVERSE (MAP embed (MAP edge rc))`; `snipr_ring` = `REVERSE r`.
  The `rev r` in `C_reducible` is `REVERSE r` in `c_reducible`.  The ring
  orientation bug from early in the project is not present in the shipped tree:
  every `rev`/`rcons`/`rot`/`rotr` of Gonthier's has its counterpart.
- Construction programs: Coq fixpoints `cpmap (s :: cp') = step s (cpmap cp')`
  process the list from the end (head = last step); HOL
  `cpmap cp = ITLIST cpstep_apply cp (cpmap0,1)` does the same
  (`ITLIST f [a;b;c] x = f a (f b (f c x))`).
  `cpcolor cp = ctree_cons_rot (cpcolor0 (REVERSE cp))`, `cfctr`, `ctrmsize`,
  `ctrenum`, `ctrband`, `cpadj`, `cpker`, `cprsize`, `cfquiz_rec`, `Birkhoff`'s
  `cpcard` all recurse on the same head-first structure as Coq.  Right-to-left
  Boolean fixpoints (`cubic_prog`, `config_prog`) are the `ALL`/`LAST`
  restatements; programs in configurations.ml are stored in Coq's written order
  and were verified identical.
- Empty-list convention: HOL `list_cycle` requires nonemptiness (ssreflect
  `cycle e [::] = true`); see 1.3.3.

### 5.4 Single dart type and minimality
All derived hypermaps keep the dart type (`edge_walkup`, `snip_disk`,
`snip_rem`, `embed_disk`, `embed_rem`, `ecp*`, `cpmap : (num)hypermap`),
except `sew_map : (A+B)hypermap` and `cube : (cube_tag#A)hypermap`.  Coq's
injections `snipd`, `embd`, `icpY`, ... are identities; `preim_seq` rings
are the rings themselves.  `minimal_counter_example` therefore ranges over
same-type hypermaps (REFORMULATED); the Birkhoff argument transfers the
sewn map back into type `A` via `hm_iso`/`sub_hypermap`, and
`FOUR_COLOR_HYPERMAP` chooses the minimal counterexample inside
`(cube_tag#A)hypermap`.  Record hierarchies (`planar_bridgeless_plain_...`)
are conjunctions; Coq section hypotheses are bundled as predicates
(`embed_context`, `sew_context`, `redpart_hyps`) or passed explicitly
(`nhub`, `p0l`, `p0r`, `red_rec`, `redp`, `rf`, `h`, `check_basis`).

### 5.5 Booleans, tables, reflection
Coq Boolean predicates are HOL propositions; `pred4 a b c d n` becomes a
range test; lookup tables become either literal case definitions
(`permc`, `addc`, `topqa`, `popqa`, `small_qarity`, `qzt_getr`) or a semantic
definition proved equal when needed (`cmp_range`, `meet_range`, `fitqa`,
`ctr_decr`, `ctree_leaf_pair`).  Coq `reflect`/inductive specification
devices (`eq3_CtreeEmpty`, `are_4_GtreeEmpty`, `sort_drules_spec`,
`Birkhoff_check` as an inductive) are existential/equational statements.

### 5.6 Naming hazards for readers of both developments
`edge H x` (HOL) is the edge ORBIT, Coq's `edge x` is `edge_map H x`;
HOL `cprsize` is the semantic ring length and HOL `cpringsize` is Coq's
`cprsize`; HOL `ctrace` is not Coq's `ctrace` (`ctrace_a` is); HOL
`trace_col` is Coq's `urtrace`; HOL `scycle H e p` takes the relation as an
argument (Coq `scycle e p` with `sfcycle f := scycle (frel f)`); HOL
`face_simple` is Coq `simple_rec`; HOL `reducibility` is Coq's
`check_reducible` on every configuration, not Coq's `reducibility`.

## 6. Coverage

Covered in full: every Coq definition outside `Let`/`Notation` in
hypermap, walkup, jordan, geometry, cube, color, coloring, patch, sew, snip,
revsnip, chromogram, kempe, ctree, gtree, dyck, initctree, initgtree,
gtreerestrict, ctreerestrict, kempetree, cfmap, configurations, cfcolor,
cfcontract, cfreducible, birkhoff, contract, embed, quiz, quiztree, cfquiz,
part, redpart, discharge, hubcap, present/combinatorial4ct, and every HOL
definition of the corresponding files, including the two data files
(configurations, discharge rules) checked by script.  Not covered: the
real-plane layer on the Coq side (HOL uses a different route; its HOL
definitions in map_defs/map_grid are listed in section 4.7, where the
correspondence of `plane_map`, `adjacent_regions` and `map_colorable` with
realplane.v is noted), the `present5..11.v`/`job*.v` scripts (proof scripts, no
definitions), and the eval/compute infrastructure of the package
(`part2_*.ml`, `compute_fast.ml`, `*_eval.ml`), which contains no new
mathematical definitions.  Verdicts were established by reading both
bodies; "FAITHFUL" for large case tables (`gtr_split`, `ctr_decr`,
`cpcolor1`, `cfctr`, `cpadj`, `red_zpart_rec`, `zstep*`, `cube_*`,
`matchg`/`matchpg`) means every branch was compared.


## Round-5 updates (2026-10-09, see ROUND5_PLAN.md and CHANGES_pkg_01.md)
- `gtree_mem` (gtree.ml): now clausal on (tree, chromogram) exactly like
  gtree.v:71 (node: step into the selected subtree; each leaf accepts its
  one-symbol chromograms; GtreeEmpty and the empty chromogram: false); the
  former if-chain with the existential `?a b c d. t = GtreeNode a b c d` is
  gone, and birkhoff.ml's GTREE_NODE_EXISTS/GTREE_MEM_CLAUSES shim reduces to
  `GTREE_MEM_CLAUSES = gtree_mem`.
- `qzt_truncate` (quiztree.ml): Gonthier's one-line `match` (see the table
  row); EXISTS_NODE deleted.
- The cpstep family (cpstep_apply, cpringsize, cpker, cubic_step, config_step,
  cpcolor1, cpcolor0, cpcard, ctrmsize, ctrenum, cfctr_ok, cfctr_map, ctrband):
  one `define` equation per constructor instead of `(?n. s = CpR n)` /
  `@n. s = CpR n` if-chains -- phase 1 (cfmap, cfcolor, birkhoff) done, phase 2
  (cfcontract) in progress at the time of writing; the per-step case-clause
  scaffolding (CPR_SELECT, case_clauses, *_CASES, *_CLAUSES) becomes the
  definitions themselves.
- Still deliberate: the quiz-layer discriminators
  isQaskR/isQaskL/isQaskLR/isCpR/isQztHubNode/isQuizR (already clausal; the
  unavoidability evaluators rewrite with predicate discriminators),
  excluded_arity's `(:A)` carrier.
- Item E DONE (2026-10-09 23:49): see 1.3.1.  Item A DONE: all 13 cpstep-family
  definitions clausal (phase 1 cfmap/cfcolor/
  birkhoff, phase 2 cfcontract); CPR_SELECT/case_clauses/*_CASES scaffolding
  deleted; cfmap's FACE_SIMPLE_APPEND renamed FACE_SIMPLE_APPEND_EQ.  The 10
  `try define_type ... with Failure _` reload guards and the guarded
  c_reducible are plain definitions now.

## Review of 2026-10-14/15
- No definition was changed in substance: every definition phrase of the
  package is textually identical to the reviewed version, except that the
  bound variable `closure` of `ktc_step`, `ktc_stepp`, `ktc_correct` and
  `ktc_apply` is now `ktc0` (so that the development parses with
  Multivariate's constant `closure` visible), so every verdict above
  stands.  Theorems were deleted, re-proved, renamed or moved, which
  shifted line numbers; the file:line references above were refreshed where
  the referenced definition (or line) could be identified unambiguously (84
  of about 245).  Many of the others were already approximate before the
  review; searching the named file for the definition's name is the
  reliable way to find it.
- The new files of the parallel variant (par_hook.ml, parallel.ml,
  part2_cost_order.ml, make_parallel.ml) define no HOL constants.

