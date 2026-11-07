(* ========================================================================= *)
(* Partial loader for the Baker core: sections 1 to 4 of Baker/make.ml, the  *)
(* library-style files, the foundations, the Baker core and the Baker        *)
(* theorems and applications (everything up to BAKER_FELDMAN, the            *)
(* applications of Baker/apps.ml, the uniform bounds of Baker/uniform.ml and *)
(* the examples of Baker/apps_examples.ml).                                  *)
(* ========================================================================= *)

needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Library-style lemmas: generic lemmas shared by all sections. Needs     *)
(*    only the library.                                                      *)
(* ------------------------------------------------------------------------- *)

needs "Baker/lemmas.ml";;

(* ------------------------------------------------------------------------- *)
(* 2. Foundations: algebraic numbers, integer polynomials, Liouville and     *)
(*    Siegel lemmas, Feldman polynomials, residues and interpolation,        *)
(*    exponential polynomials, the bridge to algebraic_number, a lower bound *)
(*    for the roots of integer polynomials. Needs only section 1.            *)
(* ------------------------------------------------------------------------- *)

needs "Baker/prelim.ml";;
needs "Baker/algebraic.ml";;
needs "Baker/intpoly.ml";;
needs "Baker/liouville_inequality.ml";;
needs "Baker/siegel.ml";;
needs "Baker/delta.ml";;
needs "Baker/residue.ml";;
needs "Baker/expoly.ml";;
needs "Baker/bridge.ml";;
needs "Baker/simple.ml";;

(* ------------------------------------------------------------------------- *)
(* 3. Baker core (Baker, Transcendental Number Theory, Ch. 3): the auxiliary *)
(*    function, its arithmetic, extrapolation, section 4, the parametric     *)
(*    core, the numeric layer and the explicit, existential and uniform core *)
(*    lower bounds. Needs only sections 1 and 2.                             *)
(* ------------------------------------------------------------------------- *)

needs "Baker/auxiliary.ml";;
needs "Baker/aux_arith.ml";;
needs "Baker/extrap.ml";;
needs "Baker/sec4.ml";;
needs "Baker/bounds.ml";;
needs "Baker/parametric_core.ml";;
needs "Baker/estimates.ml";;
needs "Baker/param.ml";;
needs "Baker/heights.ml";;
needs "Baker/numeric_dmax.ml";;
needs "Baker/explicit.ml";;

(* ------------------------------------------------------------------------- *)
(* 4. Baker theorems and applications: BAKER_FELDMAN (Thm 3.1), linear       *)
(*    independence of logarithms, Gelfond-Schneider, transcendence and       *)
(*    irrationality measures, S-unit gaps, uniform bounds for possibly       *)
(*    dependent logarithms (BAKER_UNIFORM_INTEGER, BAKER_UNIFORM_RATIONAL)   *)
(*    and the uniform core with algebraic coefficients (the coefficient data *)
(*    sharpc_coefdata, BAKER_CORE_UNIFORM_ALGCOEFF;                          *)
(*    BAKER_CORE_UNIFORM_INTEGER is its instance for integer coefficients),  *)
(*    examples. Needs only sections 1 to 3.                                  *)
(* ------------------------------------------------------------------------- *)

needs "Baker/theorem.ml";;
needs "Baker/apps.ml";;
needs "Baker/uniform.ml";;
needs "Baker/apps_examples.ml";;
