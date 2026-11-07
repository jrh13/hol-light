(* ========================================================================= *)
(* Baker theorem on linear forms in logarithms and its applications: the     *)
(* loader of the directory Baker/.                                           *)
(*                                                                           *)
(* Every file of Baker/ starts with needs lines for the files whose results  *)
(* it uses (library files, files of ANT/ and of Baker/), so that loading one *)
(* file with needs also loads its prerequisites. This loader loads all       *)
(* files, by sections, after the library prerequisites, which come first in  *)
(* an order in which they load together: Library/jacobi.ml before the        *)
(* Multivariate files, Multivariate/gamma.ml after 100/dirichlet.ml. The     *)
(* algebraic number theory files of ANT/ load through the needs lines of the *)
(* files that use them.                                                      *)
(*                                                                           *)
(* Sections: 1 library-style lemmas, 2 foundations, 3 the Baker core, 4      *)
(* Baker theorems and applications, 5 algebraic integers (the integral       *)
(* elements of C over Z of ANT/), number fields inside C and, at its end,    *)
(* the imaginary quadratic base files (binary quadratic forms, the field     *)
(* Q(sqrt(-d)) as a number field of ANT/ and its ring of integers), 6        *)
(* Sharpening I (Baker 1972) for algebraic numbers, uniform in the data,     *)
(* complex logarithms: one machinery for integer and algebraic coefficients  *)
(* and its ending for integer coefficients, 7 Sharpening I with algebraic    *)
(* coefficients (Baker 1973): the ending for algebraic coefficients, 8       *)
(* Tijdeman and the Catalan exponents (the rational case of Sharpening I), 9 *)
(* two logarithms (an explicit lower bound by interpolation determinants)    *)
(* and the Steiner theorem on the 3x+1 problem, 10 the Laurent bound for two *)
(* logarithms of rationals, 11 number fields as conjugate vectors (the       *)
(* bridge to the number fields of ANT/), Thue and Mordell equations, 12      *)
(* Lebesgue, Ko Chao, the S-unit descent, superelliptic equations and        *)
(* Catalan finiteness, 13 the Laurent bound for algebraic numbers via        *)
(* pair heights, 14 tools for the Schinzel-Tijdeman theorem (from the        *)
(* proof of its reducible case), 15 the class number one problem, 16 unique  *)
(* factorization in imaginary quadratic fields (the rings of integers of     *)
(* Q(sqrt(-d)): unique factorization iff class number one iff d = m^2 k      *)
(* with k one of the nine of Gauss; the same for every number field of       *)
(* degree 2 with negative discriminant), 17 applications of unique           *)
(* factorization (Ramanujan-Nagell, Fermat on 26, Fermat Last Theorem for    *)
(* the exponent 3), 18 the hyperelliptic equation and integral points on     *)
(* elliptic curves, 19 the prime factors of polynomial values, 20 the        *)
(* Schinzel-Tijdeman theorem (y^m = f(x) for every integer polynomial f      *)
(* with two distinct roots; the reducible case as corollaries), 21 perfect   *)
(* powers in Lucas sequences and the equations x^k + D = y^n, 22 imaginary   *)
(* quadratic fields of class number two (there are only finitely many).      *)
(*                                                                           *)
(* Partial loaders: Baker/make_core.ml (sections 1 to 4, up to BAKER_FELDMAN *)
(* and the applications), Baker/make_twolog.ml (two logarithms and Steiner:  *)
(* sections 1 and 9) and Baker/make_laurent.ml (the Laurent bound for        *)
(* rationals: sections 1, 9 and 10). Baker/README describes the main results *)
(* and Baker/OVERVIEW.md states them.                                        *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Multivariate/gamma.ml";;
needs "Examples/gcdrecurrence.ml";;

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

(* ------------------------------------------------------------------------- *)
(* 5. Algebraic integers and number fields inside C: algebraic_integer (the  *)
(*    integral elements of C over Z of ANT/integral.ml; closure under the    *)
(*    ring operations, rational algebraic integers are integers, integer     *)
(*    coefficients from integer power sums), the rings of integers of the    *)
(*    subfields of C, the prime subfield Q, finitely many algebraic numbers  *)
(*    generate a number field (NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED),     *)
(*    subrings, subfields and homomorphisms of subfields of C. At its end    *)
(*    the imaginary quadratic base files: the definitions of the binary      *)
(*    quadratic forms and of qdisc (Baker/classno_defs.ml), the field        *)
(*    Q(sqrt(-d)) as a number field of ANT/ with discriminant qdisc d        *)
(*    (IMAG_QUADRATIC_FIELD_DISCRIMINANT), its ring of integers Z[omega]     *)
(*    (IMAG_QUADRATIC_INTEGERS_CARRIER), the units, and the Euclidean        *)
(*    algorithm for d = 1, 2, 3, 7, 11 (IMAG_QUADRATIC_INTEGERS_EUCLIDEAN,   *)
(*    _PID, _UFD). Needs ANT/ and sections 1 and 2.                          *)
(* ------------------------------------------------------------------------- *)

needs "Baker/algint.ml";;
needs "Baker/ant_bridge_complex.ml";;
needs "Baker/classno_defs.ml";;
needs "Baker/quadint_defs.ml";;
needs "Baker/quadint_ant.ml";;
needs "Baker/quadint_ring.ml";;

(* ------------------------------------------------------------------------- *)
(* 6. Sharpening I (Baker 1972) for algebraic numbers, uniform in the data:  *)
(*    the machinery for integer and algebraic coefficients and the ending    *)
(*    for integer coefficients. BAKER_SHARPENING (non-zero algebraic numbers *)
(*    of degree at most d, the first n - 1 of height at most exp g0, the     *)
(*    last of height at most A, principal logarithms, integer coefficients   *)
(*    of size at most B: Lambda = 0 or |Lambda| >= exp(-C g0^K log A log B), *)
(*    C and K depending only on n and d), BAKER_SHARPENING_REAL,             *)
(*    SHARP_BAKER_NUMBER_FIELD (fixed numbers of a number field and one      *)
(*    variable number with bounded denominator and conjugates),              *)
(*    SHARP_BAKER_ALGEBRAIC. One machinery with complex coefficients bb r    *)
(*    (integer coefficients are coefficient data of degree 1,                *)
(*    SHARPC_COEFDATA_INTEGER): Delta-functions and the auxiliary function,  *)
(*    Kummer theory over any subfield of C (KUMMER_COMPLEX, from the Kummer  *)
(*    theory of Library/galois.ml), Lemmas 5, 6 and 8 over a Delta           *)
(*    representation (sharp_deltarep: the integer values of the Baker        *)
(*    binomial trick, SHARP_DELTAREP_INT, or the factorial polynomials of    *)
(*    Baker 1973, SHARP_DELTAREP_ALG), section 4 over Q(alphas, betas), the  *)
(*    extrapolation and one parametric core (SHARP_CORE_PARAMETRIC), the     *)
(*    numeric design (SHARP_CORE_DESIGN, the design facts of both endings)   *)
(*    with the numeric ending for integer coefficients                       *)
(*    (SHARP_CORE_ALGEBRAIC: log B), number field tools (denominators of     *)
(*    p-th roots by the ideal norms of ANT/, degrees, integer polynomials of *)
(*    elements with bounded conjugates), the uniform base of both endings    *)
(*    (BAKER_UNIFORM_ALGCOEFF, SHARPC_UNIFORM_ALG, with SHARP_UNIFORM_ALG as *)
(*    its instance), the shared descent tools and the descent for integer    *)
(*    coefficients. Needs ANT/ and sections 1 to 5.                          *)
(* ------------------------------------------------------------------------- *)

needs "Baker/sharp_poly.ml";;
needs "Baker/sharp_defs.ml";;
needs "Baker/sharp_aux.ml";;
needs "Baker/kummer.ml";;
needs "Baker/sharp_arith.ml";;
needs "Baker/sharp_sec4.ml";;
needs "Baker/sharp_core.ml";;
needs "Baker/sharp_num.ml";;
needs "Baker/sharp_tools.ml";;
needs "Baker/sharp_uniform.ml";;
needs "Baker/sharp_descent.ml";;
needs "Baker/sharp_main.ml";;

(* ------------------------------------------------------------------------- *)
(* 7. Sharpening I with algebraic coefficients (Baker, A central theorem in  *)
(*    transcendence theory, 1973; Transcendental Number Theory, p. 23),      *)
(*    uniform in the data: the ending for algebraic coefficients of the      *)
(*    machinery of section 6. BAKER_SHARPENING_ALGEBRAIC_COEFFS (non-zero    *)
(*    algebraic numbers of degree at most d, the first n - 1 of height at    *)
(*    most exp g0, the last of height at most A, principal logarithms,       *)
(*    algebraic coefficients of degree at most d and height at most B:       *)
(*    Lambda = 0 or |Lambda| >= exp(-C g0^K log A log(B log A)), C and K     *)
(*    depending only on n and d), SHARPC_SHARPENING_REAL, SHARPC_BAKER; the  *)
(*    numeric ending for algebraic coefficients (SHARPC_CORE: the bound      *)
(*    functions of the factorial Delta representation are dominated by those *)
(*    of the integer one at the analytic size Bp = (2 Lm + S0) (1 + D)^n     *)
(*    B^(3n), the source of log(B log A)) and the normalised descent         *)
(*    (bb n = 1) in the fixed field Q(alphas, betas). Needs ANT/ and         *)
(*    sections 1 to 6.                                                       *)
(* ------------------------------------------------------------------------- *)

needs "Baker/sharpc_num.ml";;
needs "Baker/sharpc_descent.ml";;
needs "Baker/sharpc_main.ml";;

(* ------------------------------------------------------------------------- *)
(* 8. Tijdeman (1976) and the Catalan exponents: SHARP_BAKER_RATIONAL and    *)
(*    TIJDEMAN_LINEAR_FORMS_RATIONAL (the rational case of Sharpening I:     *)
(*    BAKER_SHARPENING_REAL with d = 1), CATALAN_EXPONENT_BOUND. Needs       *)
(*    ANT/ and sections 1 to 6.                                              *)
(* ------------------------------------------------------------------------- *)

needs "Baker/catalan_nt.ml";;
needs "Baker/catalan.ml";;
needs "Baker/tijdeman.ml";;

(* ------------------------------------------------------------------------- *)
(* 9. Two logarithms: an explicit lower bound for linear forms in two        *)
(*    logarithms (interpolation determinants; the determinants are ring_det  *)
(*    of Library/ring_det.ml over complex_ring and real_ring,                *)
(*    COMPLEX_RING_DET, REAL_RING_DET), and the Steiner theorem on the       *)
(*    circuits of the 3x+1 problem. Needs only section 1                     *)
(*    (Baker/make_twolog.ml).                                                *)
(* ------------------------------------------------------------------------- *)

needs "Baker/twolog_det.ml";;
needs "Baker/twolog_interp.ml";;
needs "Baker/twolog_zero.ml";;
needs "Baker/twolog_core.ml";;
needs "Baker/twolog_param.ml";;
needs "Baker/twolog.ml";;
needs "Baker/steiner.ml";;

(* ------------------------------------------------------------------------- *)
(* 10. The Laurent bound for two logarithms of rationals (Laurent 2008 at    *)
(*     mu = 1): LAURENT_RATIONAL, LAURENT_RATIONAL_GENERAL,                  *)
(*     LAURENT_RATIONAL_PARAM. Needs only sections 1 and 9                   *)
(*     (Baker/make_laurent.ml).                                              *)
(* ------------------------------------------------------------------------- *)

needs "Baker/laurent_defs.ml";;
needs "Baker/laurent_det.ml";;
needs "Baker/laurent_binom.ml";;
needs "Baker/laurent_glemma.ml";;
needs "Baker/laurent_interp.ml";;
needs "Baker/laurent_core.ml";;
needs "Baker/laurent_param_main.ml";;
needs "Baker/laurent_param.ml";;
needs "Baker/laurent_corner.ml";;
needs "Baker/laurent.ml";;

(* ------------------------------------------------------------------------- *)
(* 11. Number fields as conjugate vectors and their orders, the bridge       *)
(*     between ANT/ and the conjugate-vector number fields (nf_data gives a  *)
(*     number field of degree n with the n embeddings nf_embedding; nf_elem, *)
(*     nf_alg_int, nf_order and nf_unit are the conjugate vectors of K, O_K, *)
(*     Z[r 1] and its units; the product and the sum of the conjugates are   *)
(*     the norm and the trace; the Northcott finiteness of the order from    *)
(*     that of O_K), units, Thue equations, cubic forms, Mordell equations   *)
(*     (the algebraic integers are in section 5). The bridge                 *)
(*     Baker/ant_bridge_nf.ml and the definitions Baker/laurent_nf_defs.ml   *)
(*     of the Laurent bound for algebraic numbers load here, after           *)
(*     Baker/nf_order.ml. Needs ANT/ and sections 1 to 6 (Baker/nf_box.ml    *)
(*     uses RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED of                   *)
(*     Baker/sharp_tools.ml).                                                *)
(* ------------------------------------------------------------------------- *)

needs "Baker/nf_defs.ml";;
needs "Baker/nf_order.ml";;
needs "Baker/laurent_nf_defs.ml";;
needs "Baker/ant_bridge_nf.ml";;
needs "Baker/nf_box.ml";;
needs "Baker/nf_units.ml";;
needs "Baker/thue.ml";;
needs "Baker/cubic_reduction.ml";;
needs "Baker/mordell.ml";;

(* ------------------------------------------------------------------------- *)
(* 12. Lebesgue and Ko Chao, the S-unit descent in a number field inside C   *)
(*     (Baker/schinzel_sunit.ml, with the descent for one root used by       *)
(*     section 20), the descent, primitive elements, the unit equation,      *)
(*     superelliptic equations, Catalan finiteness. LEBESGUE uses the        *)
(*     Gaussian integers as the Euclidean ring imag_quadratic_integers 1     *)
(*     (the imaginary quadratic base files of section 5). Needs ANT/ and     *)
(*     sections 1 to 6, 8 and 11.                                            *)
(* ------------------------------------------------------------------------- *)

needs "Baker/lebesgue.ml";;
needs "Baker/kochao.ml";;
needs "Baker/schinzel_sunit.ml";;
needs "Baker/descent.ml";;
needs "Baker/nf_fields.ml";;
needs "Baker/uniteq.ml";;
needs "Baker/superell_descent.ml";;
needs "Baker/superell_roots.ml";;
needs "Baker/superell.ml";;
needs "Baker/catalan_finite.ml";;

(* ------------------------------------------------------------------------- *)
(* 13. The Laurent bound for algebraic numbers via pair heights:             *)
(*     LAURENT_NF_REAL, LAURENT_NF_REAL_PARAM (the definitions               *)
(*     Baker/laurent_nf_defs.ml are in section 11). Needs ANT/ and           *)
(*     sections 1, 2, 5 and 9 to 11.                                         *)
(* ------------------------------------------------------------------------- *)

needs "Baker/laurent_nf.ml";;
needs "Baker/laurent_alg.ml";;

(* ------------------------------------------------------------------------- *)
(* 14. Tools for the Schinzel-Tijdeman theorem, from the proof of its        *)
(*     reducible case (whose theorems SCHINZEL_TIJDEMAN_REDUCIBLE,           *)
(*     SCHINZEL_TIJDEMAN_FINITE_REDUCIBLE, SCHINZEL_TIJDEMAN_REDUCIBLE_MULT  *)
(*     are corollaries in section 20): the bounded power descent over Z      *)
(*     (INT_POWER_DESCENT_BOUNDED), logarithms of monic polynomials,         *)
(*     exponent bounds, the monic scaling, the multiplicity split and the    *)
(*     root data of integer polynomials, used by sections 19 and 20. Needs   *)
(*     ANT/ and sections 1 to 6, 11 and 12.                                  *)
(* ------------------------------------------------------------------------- *)

needs "Baker/schinzel_descent.ml";;
needs "Baker/schinzel_poly.ml";;
needs "Baker/schinzel.ml";;
needs "Baker/schinzel_mult.ml";;

(* ------------------------------------------------------------------------- *)
(* 15. The class number one problem (Baker 1966 / Gauss): imaginary          *)
(*     quadratic fields of class number one: CLASS_NUMBER_ONE (exactly the   *)
(*     nine d = 1, 2, 3, 7, 11, 19, 43, 67, 163),                            *)
(*     CLASS_NUMBER_ONE_BOUND_LAURENT (d < 10^16 by the Laurent bound),      *)
(*     CLASS_NUMBER_ONE_FINITE. With the general machinery of binary         *)
(*     quadratic forms shared with section 22: reduction, the evaluator of   *)
(*     form_classno (QF_FORMS_EVAL, FORM_CLASSNO_CONV), representation       *)
(*     numbers, the lattice series of a positive definite form twisted by a  *)
(*     real character and the limit formula at s = 1                         *)
(*     (Baker/qform_limit.ml, Baker/qform_series.ml), from which the         *)
(*     identity for the principal form follows (Baker/classno_product.ml).   *)
(*     Needs Library/jacobi.ml, 100/dirichlet.ml and Multivariate/gamma.ml   *)
(*     (Jacobi symbols, Dirichlet L-functions, the sine product); ANT/ and   *)
(*     sections 1 to 6, 9 to 11 and 13 (with the definitions                 *)
(*     Baker/classno_defs.ml at the end of section 5, and Baker/kummer.ml of *)
(*     section 6 for CLASSNO_NF_SQRT_INDEPENDENT).                           *)
(* ------------------------------------------------------------------------- *)

needs "Baker/classno_forms.ml";;
needs "Baker/classno_chardefs.ml";;
needs "Baker/classno_rep.ml";;
needs "Baker/classno_series_lib.ml";;
needs "Baker/classno_series.ml";;
needs "Baker/classno_poisson.ml";;
needs "Baker/classno_limit.ml";;
needs "Baker/classno_gauss.ml";;
needs "Baker/qform_limit.ml";;
needs "Baker/qform_series.ml";;
needs "Baker/classno_product.ml";;
needs "Baker/classno_cyclo.ml";;
needs "Baker/classno_nf.ml";;
needs "Baker/classno_cf.ml";;
needs "Baker/classno_linear.ml";;
needs "Baker/classno_main.ml";;

(* ------------------------------------------------------------------------- *)
(* 16. Unique factorization in imaginary quadratic fields: the field         *)
(*     Q(sqrt(-d)) as a number field of ANT/ (the field, its discriminant    *)
(*     qdisc d and its ring of integers Z[omega] are the imaginary quadratic *)
(*     base files at the end of section 5): the ring of integers is a UFD,   *)
(*     equivalently a PID, equivalently of class number one, iff d = m^2 k   *)
(*     with k in the nine of Gauss: CLASS_NUMBER_ONE_UFD,                    *)
(*     CLASS_NUMBER_ONE_PID, CLASS_NUMBER_ONE_IDEAL_CLASSES,                 *)
(*     CLASS_NUMBER_ONE_UNIQUE_FACTORIZATION; for every number field of      *)
(*     degree 2 with negative discriminant d_k: class number one iff d_k is  *)
(*     one of the nine discriminants (IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE). *)
(*     Needs ANT/ and sections 1 to 6, 9 to 11, 13 and 15 (section 5: number *)
(*     fields inside C, rings of integers are algebraic integers, the prime  *)
(*     subfield is Q; the imaginary quadratic base files).                   *)
(* ------------------------------------------------------------------------- *)

needs "Baker/quadint_ufd.ml";;
needs "Baker/quadint_pid.ml";;
needs "Baker/quadint_main.ml";;
needs "Baker/quadint_intrinsic.ml";;

(* ------------------------------------------------------------------------- *)
(* 17. Diophantine applications of unique factorization in imaginary         *)
(*     quadratic fields: RAMANUJAN_NAGELL (x^2 + 7 = 2^n),                   *)
(*     FERMAT_SQUARE_CUBE and FERMAT_26 (x^2 + 2 = y^3), FLT3 (Fermat Last   *)
(*     Theorem for the exponent 3). Needs only ANT/ufd.ml and the imaginary  *)
(*     quadratic base files at the end of section 5 (unique factorization    *)
(*     from the Euclidean algorithm, IMAG_QUADRATIC_INTEGERS_UFD):           *)
(*     sections 1, 2 and 5.                                                  *)
(* ------------------------------------------------------------------------- *)

needs "Baker/ramanujan_nagell.ml";;
needs "Baker/fermat26.ml";;
needs "Baker/flt3.ml";;

(* ------------------------------------------------------------------------- *)
(* 18. The hyperelliptic equation (Baker 1969) and integral points on        *)
(*     elliptic curves (Baker 1968): HYPERELLIPTIC,                          *)
(*     SUPERELLIPTIC_SIMPLE_ROOTS (all m >= 2), ELLIPTIC_INTEGRAL_POINTS,    *)
(*     ELLIPTIC_CUBIC_INTEGRAL_POINTS, WEIERSTRASS_INTEGRAL_POINTS. Needs    *)
(*     ANT/ and sections 1 to 6, 11 and 12.                                  *)
(* ------------------------------------------------------------------------- *)

needs "Baker/hyperell_roots.ml";;
needs "Baker/hyperell.ml";;
needs "Baker/elliptic.ml";;

(* ------------------------------------------------------------------------- *)
(* 19. The prime factors of the values of an integer polynomial with two     *)
(*     distinct roots, a classical theorem (Polya, Siegel):                  *)
(*     POLY_SMOOTH_VALUES_FINITE (only finitely many x with f(x) <> 0 and    *)
(*     all prime factors in a finite set S), POLY_LARGEST_PRIME_FACTOR (the  *)
(*     greatest prime factor of f(x) tends to infinity),                     *)
(*     POLY_SMOOTH_VALUES_FINITE_SIMPLE, POLY_PRIME_POWER_VALUES_FINITE and  *)
(*     the corollaries for x^2 + D; through SUPERELLIPTIC (m = 3). Needs     *)
(*     ANT/ and sections 1 to 6, 11, 12 and 14.                              *)
(* ------------------------------------------------------------------------- *)

needs "Baker/prime_factors.ml";;

(* ------------------------------------------------------------------------- *)
(* 20. The Schinzel-Tijdeman theorem (Acta Arith. 31, 1976):                 *)
(*     SCHINZEL_TIJDEMAN (f with integer coefficients and two distinct       *)
(*     complex roots, of any multiplicities: the integer solutions of        *)
(*     y^m = f(x) with |y| >= 2 have bounded m), SCHINZEL_TIJDEMAN_FINITE    *)
(*     (two simple roots: finitely many solutions with m >= 3),              *)
(*     SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS, SQUARE_PLUS_POW_FINITE         *)
(*     (x^2 + D = y^n with D <> 0); per root the S-unit descent with         *)
(*     ANT/ (SCHINZEL_TIJDEMAN_ROOT_DESCENT of Baker/schinzel_sunit.ml,      *)
(*     section 12), then one linear form in logarithms for any two distinct  *)
(*     roots, bounded below by SHARP_BAKER_NUMBER_FIELD; the reducible case  *)
(*     (SCHINZEL_TIJDEMAN_REDUCIBLE, SCHINZEL_TIJDEMAN_FINITE_REDUCIBLE,     *)
(*     SCHINZEL_TIJDEMAN_REDUCIBLE_MULT) as corollaries. Needs ANT/ and      *)
(*     sections 1 to 6, 11, 12, 14, 18 and 19.                               *)
(* ------------------------------------------------------------------------- *)

needs "Baker/schinzel_general.ml";;

(* ------------------------------------------------------------------------- *)
(* 21. Perfect powers in Lucas sequences and the equations x^k + D = y^n,    *)
(*     applications of the Schinzel-Tijdeman theorem:                        *)
(*     LUCAS_PERFECT_POWERS_FINITE (u_0 = 0, u_1 = 1, u_(n+2) = P            *)
(*     u_(n+1) - Q u_n with Q = 1 or Q = -1 and P^2 <> 4 Q: only finitely    *)
(*     many perfect powers y^m with |y| >= 2, m >= 2),                       *)
(*     LUCAS_COMPANION_PERFECT_POWERS_FINITE (v_0 = 2, v_1 = P, every P),    *)
(*     FIBONACCI_PERFECT_POWERS_FINITE (fib of Examples/gcdrecurrence.ml),   *)
(*     PELL_PERFECT_POWERS_FINITE, LUCAS_NUMBERS_PERFECT_POWERS_FINITE,      *)
(*     POW_PLUS_POW_FINITE (x^k + D = y^n for fixed k >= 2 and D <> 0),      *)
(*     SQUARE_PLUS_MUL_POW_FINITE (x^2 + C = D y^n, n >= 3). Needs ANT/      *)
(*     and sections 1 to 6, 11, 12, 14 and 18 to 20                          *)
(*     (SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA is in section 19) and         *)
(*     Examples/gcdrecurrence.ml.                                            *)
(* ------------------------------------------------------------------------- *)

needs "Baker/perfect_powers.ml";;

(* ------------------------------------------------------------------------- *)
(* 22. Imaginary quadratic fields of class number two (Baker 1971, Stark     *)
(*     1971; Baker, Transcendental Number Theory, Ch. 5, sec. 5):            *)
(*     CLASS_NUMBER_TWO_FINITE (only finitely many squarefree d with         *)
(*     form_classno (qdisc d) = 2), CLASS_NUMBER_TWO_FINITE_ODD,             *)
(*     CLASS_NUMBER_TWO_EXAMPLES (the eighteen known d have class number     *)
(*     two); genus theory for class number two by witnesses                  *)
(*     (CN_FORMS_TWO_CASES, CN_GENUS_CHARACTER), the representation numbers  *)
(*     of the two forms of discriminant -d and -4d, the genus and total      *)
(*     product identities of L-series at s = 1 (with the general form        *)
(*     machinery of section 15), the cyclotomic unit lemma                   *)
(*     (CN_CYCLO_UNIT_QUADRATIC) and |L(1,chi)| <= log m + 3, the class      *)
(*     number formula for the odd characters of even modulus,                *)
(*     zeta(2) = pi^2/6, the three linear forms in logarithms                *)
(*     (CN_LINEAR_MAIN, CN_LINEAR_SMALL, CN_LINEAR_EVEN), closed by          *)
(*     BAKER_SHARPENING_ALGEBRAIC_COEFFS (section 7) and BAKER_FELDMAN.      *)
(*     Needs ANT/ and sections 1 to 7, 9 to 11, 13 and 15.                   *)
(* ------------------------------------------------------------------------- *)

needs "Baker/cn_defs.ml";;
needs "Baker/cn_forms.ml";;
needs "Baker/cn_rep.ml";;
needs "Baker/cn_cyclo.ml";;
needs "Baker/cn_gauss_even.ml";;
needs "Baker/cn_rep_even.ml";;
needs "Baker/cn_zeta.ml";;
needs "Baker/cn_products.ml";;
needs "Baker/cn_linear.ml";;
needs "Baker/cn_main.ml";;
