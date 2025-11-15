# TacticTrace

This tool detects definitions of HOL Light tactics/conversions as well as their users,
and patches proof files so that

* Tactics log the input and output goals
* Conversions log the input term and output theorem

in the JSON format.

Also, this tool provides a tool for collecting top-level theorems that are defined
as `let <theorem> = prove(<goal>, <proof>);;` and dumping in the JSON format.

## Prerequisite

This project does not need patching HOL Light.
Instead, HOL Light must be built with OCaml 5.2.0 (the `make switch-5` as of
Aug. 22, 2025) and compiled with `HOLLIGHT_USE_MODULE=1`.

**Operating System.**
TacticTrace is tested on Ubuntu and MacOS.

## 1. Building trace-generating tactic/conv wrappers of the HOL Light kernel

```sh
make

export HOLLIGHT_DIR=<the HOL Light dir>
export TACLOGGER_DIR=${HOLLIGHT_DIR}/TacticTrace
./build-hol-kernel.sh
```

This will create `kernel_wrapper.ml` which will be used in the next step.

## 2. Collecting the traces of tactic/conversion

Let's assume that you want have a HOL Light proof file `a.ml`.
You will need to inline `loadt`/`loads`/`needs` invocations in `a.ml` through the following
OCaml script which is provided by HOL Light:

```sh
ocaml ${HOLLIGHT_DIR}/inline_load.ml a.ml a_inlined.ml
```

The next step is to modify the definitions of tactics/conversions as well as their
users in `a_inlined.ml` so that they emit the inputs and outputs to a JSON file.

```sh
${TACLOGGER_DIR}/modify-proof.sh a_inlined.ml a_inlined_wrapped.ml /home/your/output/dir
```

You can run the `a_inlined_wrapped.ml` by loading it on top of HOL Light REPL (`hol.sh`), or
building it using the OCaml compiler. The following commands show how to build it using the OCaml
native compiler.

```sh
eval $(opam env --switch $HOLLIGHT_DIR --set-switch)

# Give a large stack size.
OCAMLRUNPARAM=l=2000000000 \
ocamlopt.byte -pp "$(${HOLLIGHT_DIR}/hol.sh -pp)" -I "${HOLLIGHT_DIR}" -I +unix -c \
    hol_lib.cmxa a_inlined_wrapped.ml -o a_inlined_wrapped.cmx -w -a
ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa \
    -I "${HOLLIGHT_DIR}" a_inlined_wrapped.cmx \
    -o "a_inlined_wrapped.native"
```

## 3. Collecting top-level theorems

Given an inlined HOL Light proof `a_inlined.ml`, you can use `tracer collect-top-level-thms` to
collect information of the top-level theorems.

For example, if `a_inlined.ml` contains:

```
...
let MY_THM = prove(
  `forall x, x + 1 = 1 + x`,
  ARITH_TAC);;
```

Running the following commands will save a JSON file that contains the line number
informations of theorems including `MY_THM`.

```
./get-ast.sh a_inlined.ml # This creates a_inlined.marshalled.bin
./tracer collect-toplevel-thms a_inlined.marshalled.bin output.json
```

### Known limitations

**Correctness of line/column number information of the goal.**
If the goal term of a theorem consists of multiple lines, e.g.,

```
prove(`forall x,
x + 1 = 1 + x`,
    (my tac))
```

You will observe that the column number and line number does not exactly match.
This is because the source code preprocessor of HOL Light first replaces line breaks
in a term with spaces, as follows:

```
prove(`forall x, x + 1 = 1 + x`,
    (blank line)
    (my tac))
```

Therefore, if you want to extract the string representation of goal from the source code,
`goal_linenum_end` and `goal_colnum_end` should be properly adjusted.

**Theorems inside modules.**
TacticTrace will not catch tactics that are defined inside a module.

## Author and contact

Juneyoung Lee, aqjune@gmail.com
