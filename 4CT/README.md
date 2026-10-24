# 4CT: the Four Colour Theorem in HOL Light

`make.ml` loads the whole development and leaves the theorem for
hypermaps, planar graphs and plane maps,

    FOUR_COLOR : |- !H:(A)hypermap. planar_hypermap H /\ bridgeless H
                    ==> four_colorable H

    FOUR_COLOR_PLANAR_GRAPH :
      |- !V E. planar_graph V E
               ==> ?c. (!v. v IN V ==> c v < 4) /\
                       (!u v. {u,v} IN E ==> ~(c u = c v))

    FOUR_COLOR_MAP : |- !M. plane_map M ==> map_colorable 4 M

with no hypotheses.  Part 1 is the mathematics: sections A-G follow
Gonthier's Coq proof (hypermaps and their geometry, colourings, walkup,
Jordan, Kempe chains; surgery and configuration maps; colouring trees and
the Kempe-closure tree; Birkhoff, the embedding morphism, contracts; the
bridge from the reducibility check; parts, quizzes, cubification, the 633
configurations; unavoidability), and sections P and M derive the
planar-graph form over the definition of HOL Light's
`Autoformalization/planar_graph.ml` (loaded first, with Multivariate), with
`FOUR_COLOR_KURATOWSKI` and `FOUR_COLOR_WAGNER` for graphs with no
subdivision or minor of K5 or K3,3, and the theorem for maps of regions in
the plane: every set of pairwise disjoint open connected subsets of the
plane (finite or not) has a colouring with four colours giving different
colours to any two regions that share a border point lying in the closure
of no third region (`map_defs.ml`, `map_grid.ml`, `map_main.ml`,
`four_color_map.ml`).  Part 2, section H, is the reducibility computation
(a compiled evaluator run over the 633 configurations) and the final
assembly.

Every load uses a `4CT/<file>` path, so the directory containing `4CT` must
be on HOL Light's load path: install `4CT` under the HOL Light root, beside
`Autoformalization` and `eval_compile`, or start HOL Light in a directory
containing all three (the default load path contains `.`).  Then, with
`ulimit -s unlimited`:

    loadt "4CT/make.ml";;

`Makefile` has the native (ocamlopt) route, 5-6x faster (`make native`,
`make run-native`; `make clean` removes the build products); compiling the
native binary takes about 2.5 hours and 50 GB, since Multivariate is
inlined.  `make native-hypermap` and `make run-native-hypermap` build and
run just the hypermap theorem FOUR_COLOR, without Multivariate
(`part2_final.ml` loaded on its own; the compile takes about 7 minutes).
`make compiled` regenerates the generated evaluator `part2_compiled.hl` from
the definitions (bytecode; it loads the development first and then re-wraps
the generated code with `reflow79.py`, whitespace only, about 15 minutes);
`make clobber` is `make clean` that also removes it, and the native builds
then regenerate it first.  `EFFICIENCY_NOTES.md` records the cost
measurements; `DEFINITION_ALIGNMENT.md` and `THEOREM_ALIGNMENT.md` map every
definition and every lemma of Gonthier's Coq proof to its counterpart here
(or explain its absence).  No OCaml standard-library function newer than
OCaml 4.03 is used outside `parallel.ml`, which only the parallel variant
below loads.  `eval_compile/`, a directory of its own beside `4CT` in the
HOL Light root, is Alexey Solovyev's compute-hol-light (MIT licence), the
proof-producing evaluator used for the computation.

With OCaml 5 or later, `make_parallel.ml` proves the same theorems with the
computations spread over the cores of one process: it loads `parallel.ml`,
which switches `present_eval.ml` (the side conditions of the presentation
scripts) and `part2_run.ml` (the 633 checks of Part 2) to their parallel
mode through the hooks of `par_hook.ml`, and then `make.ml` itself.  The
jobs run in FOURCOLOR_DOMAINS OCaml domains (default the number of cores, at
most 128).  Every theorem is still built by the kernel, so nothing depends
on the scheduling.  The Makefile uses the parallel variant when ocamlopt is
version 5 or later and the sequential one otherwise (`PARALLEL=no` forces
the latter).  On a 192-core machine (128 domains, about 48 GB) the native
run takes about 22 minutes instead of about 11 hours (EFFICIENCY_NOTES.md,
section 14).

Conventions.  Every file is 7-bit ASCII with lines of at most 79 columns.
Each file's `needs` header lists every earlier file it depends on, so any
file can be loaded on its own (with its prerequisites) in load-path order.
The file names and the definitions mirror Gonthier's `fourcolor` theories
(hypermap.v ... combinatorial4ct.v); definitions by cases are written as
one equation per constructor, as in the Coq source.  Theorem names are
unique across the package; a few suffixes recur: `_GEN` for a lemma proved
without the cubic hypothesis of its namesake, `_CF` for the cubic-free
assembly in cfcontract.ml, `_EQ` for the biconditional form of an
implication of the same name, `_ALT` for a variant with different binder
order, `_NUM` for a numeral-pattern form used by the evaluator.
