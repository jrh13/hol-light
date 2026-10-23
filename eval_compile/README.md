Proof-producing evaluation in HOL Light: eval_compile
=====================================================

Alexey Solovyev's compiler of HOL Light equational theorems into OCaml
functions that evaluate them by primitive inference.  A rule database of
equational theorems is built, and some or all of its rules are compiled into
OCaml code, which can be saved in a file.  Each compiled call instantiates a
clause theorem with the evaluated arguments and chains the results with the
kernel rules (TRANS, MK_COMB, ...), so every result is a HOL Light theorem.

The Four Colour Theorem development uses it to generate its reducibility
evaluator: 4CT/part2_eval.ml builds the rule database, 4CT/part2_compile.ml
compiles it into 4CT/part2_compiled.hl.

With the HOL Light root on the load path (the default):

    needs "eval_compile/eval_compile.hl";;     (* the compiler *)
    needs "eval_compile/eval_default_db.hl";;  (* a default rule database *)

Upstream's examples/compile.hl walks through the workflow.

Origin
------

The six .hl files and LICENSE are the top-level files of compute-hol-light,
https://github.com/hol-light-family/compute-hol-light, at master 67addec
(2026-09-30).  This copy differs from them only in:

- the `needs` paths, which are relative to the HOL Light root
  (`needs "eval_compile/eval_support.hl"` for upstream's
  `needs "eval_support.hl"`);
- `compare` in place of `Stdlib.compare` (six times in eval_support.hl,
  once in eval_database.hl, and once in the code that eval_compile.hl
  generates), because the Stdlib module needs OCaml 4.07 or later;
- layout: header boxes re-padded and long lines wrapped to 79 columns
  (including two backslash-newline continuations inside string literals in
  eval_compile.hl, which leave the strings unchanged), and trailing blanks
  removed;
- a note at the top of each file saying so.

A comparison of the token streams with upstream's shows no other
difference.  Not copied: upstream's README.md, Makefile, examples/,
scripts/, tests/ and tame/ (a port of the Isabelle enumeration of tame
graphs from the Flyspeck project).

Copyright / License
-------------------

Copyright (c) 2018 Alexey Solovyev.  Distributed under the MIT licence; see
LICENSE.
