# Sieve: sieve methods and the primes in HOL Light

Formal proofs, from HOL Light's three standard axioms, of Chen's theorem
in its Goldbach and twin prime forms and of a body of classical results
around it: the sieve framework (the beta-sieve and the Jurkat-Richert
theorem, Selberg's and Brun's sieves), the analytic input (Dirichlet
characters and L-functions, Siegel's theorem, the zero-free region,
Siegel-Walfisz, the large sieve, Bombieri-Vinogradov), the classical
corollaries, bounded gaps between primes, Vinogradov's three primes
theorem, Waring's problem, and progressions of primes up to the Green-Tao
theorem.

`make.ml` loads the whole directory.  Notation: `almost_prime k n`
means that n is a product of at least one and at most k primes, not
necessarily distinct; `pi_upto x` and `pi_ap x d a` count the primes up to
x and those that are congruent to a modulo d.

## Chen's theorem

    CHEN : ?N0. !N. EVEN N /\ N0 <= N
                    ==> ?p q. prime p /\ almost_prime 2 q /\ p + q = N

    CHEN_TWIN_INFINITE : INFINITE {p | prime p /\ almost_prime 2 (p + 2)}

with the lower bounds of the right order: `CHEN_GOLDBACH` (at least
c N / log^2 N representations N = p + P2), `CHEN_TWIN`, and `CHEN_SHIFT`
(at least c x / log^2 x primes p <= x with p + h = P2, for every even
h > 0).  `CHEN_DISTINCT` and `CHEN_TWIN_DISTINCT` (`chen_distinct.ml`) have
q a prime or a product of two distinct primes.

## The sieve and the analytic input

- `JURKAT_RICHERT` (`jurkat.ml`): the linear sieve with the upper and lower
  bound functions F, f (`dde.ml`), for any density g satisfying the
  classical dimension condition, uniformly in g; from Rosser's beta-sieve
  with beta = 2 (`ROSSER_SIEVE_UPPER`, `ROSSER_SIEVE_LOWER`, `sieve.ml`).
- `SELBERG_SIEVE` (`selberg.ml`); `BRUN`: the sum of 1/p over the twin
  primes converges, with `TWIN_PRIMES_COUNT` (`brun.ml`);
  `GOLDBACH_SHNIRELMAN` (`goldbach_shnirelman.ml`).
- Chen's weighted sieve (`chen_*.ml`): `CHEN_GENERAL` for any shift, and
  p + P4 from the lower bound sieve alone (`GOLDBACH_P4`, `TWIN_P4`).
- `SIEGEL_WALFISZ` (`sw.ml`):

      !A B. ?C. !x q c. &2 <= x /\ 1 <= q /\ &q <= log x pow B /\
                        dirichlet_character q c /\ ~(c = chi_0 q)
                        ==> norm(vsum {p | prime p /\ &p <= x} c) <=
                            C * x / log x pow A

- `BOMBIERI_VINOGRADOV` (`bv.ml`):

      !A. ?B C. !x a.
              2 <= x /\ (!d. coprime(a d,d))
              ==> sum {d | 1 <= d /\ &d <= sqrt(&x) / log(&x) pow B}
                      (\d. abs(&(pi_ap x d (a d)) - &(pi_upto x) / &(phi d)))
                  <= C * &x / log(&x) pow A

- Below them: Dirichlet series and L-functions (`dseries.ml`, `lfun.ml`,
  with the 3-4-1 inequality `THREE_FOUR_ONE`), primitive and induced
  characters (`characters.ml`), a smoothed truncated Perron formula
  (`perron.ml`), Siegel's theorem `SIEGEL` (`siegel.ml`), the zero-free
  region `ZF_RECT` (`zerofree.ml`), Vaughan's identity (`vaughan.ml`),
  Gauss sums (`gauss.ml`), the large sieve inequality in its additive and
  multiplicative forms (`LARGE_SIEVE_MULTIPLICATIVE`, `largesieve.ml`) and
  the bilinear form inequality `BILINEAR_BV` ([N] Theorem 10.7,
  `bilinear.ml`).

## Classical corollaries

- `PNT_AP` (`pnt_ap.ml`): pi(x; q, a) / (x / log x) tends to 1 / phi(q) for
  a coprime to q, with an error O(x / log^A x) (`PRIMES_AP_ERROR`).
- `BRUN_TITCHMARSH` (`brun_titchmarsh.ml`): pi(x; q, a) <= (2 + e) x /
  (phi(q) log(x / q)) for x >= y(e) q.
- `ERDOS_PRIME_PLUS_POW2` (`erdos_covering.ml`): no n congruent to 7629217
  modulo 11184810 is a prime plus a power of 2.
- `ROMANOV` (`romanov.ml`): for a >= 2 a positive proportion of the
  numbers are of the form p + a^k.
- `TITCHMARSH_DIVISOR` (`titchmarsh.ml`): sum_{p <= x} tau(p - 1) / x tends
  to zeta(2) zeta(3) / zeta(6).
- `HARDY_RAMANUJAN` (`hardy_ramanujan.ml`): omega(n) has normal order
  log log n (Turan's proof).

## Further applications

- `MAYNARD_TAO` and `BOUNDED_GAPS` (`bounded_gaps.ml`, Maynard's method at
  level of distribution 1/2 from Bombieri-Vinogradov):

      MAYNARD_TAO : !m. ?H. INFINITE {p | prime p /\
                                     m <= CARD {q | prime q /\ p <= q /\
                                                    q <= p + H}}

  with explicit H (`MAYNARD_TAO_EXPLICIT`, `BOUNDED_GAPS_EXPLICIT`) and
  for consecutive primes (`BOUNDED_GAPS_CONSECUTIVE`).
- `VINOGRADOV` (`vinogradov.ml`): every large odd number is a sum of three
  primes; `GOLDBACH_ALMOST_ALL` (`goldbach_almost.ml`): the even n <= N
  that are not a sum of two primes number O(N / log^A N) for every A.
- `WARING_HARDY_LITTLEWOOD` (`waring.ml`): G(k) <= 2^k + 1, with a lower
  bound c N^(s/k - 1) for the number of representations
  (`WARING_COUNT_LOWER`), and `HILBERT_WARING`:
  `!k. 1 <= k ==> ?g. !n. ?x. n = nsum(1..g) (\i. x i EXP k)`.
- `LINNIK_NONRESIDUE` (`linnik.ml`): for e > 0, boundedly many primes
  p <= N have no quadratic nonresidue <= N^e.
- `BARBAN_DAVENPORT_HALBERSTAM` (`bdh.ml`), by Gallagher's proof.
- `HUA_FIVE_PRIME_SQUARES` (`hua.ml`): every large N congruent to 5 modulo
  24 is a sum of five squares of primes.
- `SQUARE_PLUS_ONE_P4` and `SQUARE_PLUS_ONE_P3` (`square_plus_one.ml`,
  `square_plus_one_p3.ml`): infinitely many n with n^2 + 1 a product of at
  most four, resp. three, primes, with lower bounds c M / log M.

## Progressions of primes

- `VAN_DER_CORPUT` (`van_der_corput.ml`): infinitely many three-term
  progressions of primes, at least c N^2 / log^3 N up to N.
- `GREEN_TAO` (`gt_green_tao.ml`): `!k. ?a d. 0 < d /\ !j. j < k ==>
  prime(a + j * d)`, in the general form of Green and Tao for dense sets
  of primes with their lower bound for the number of progressions:

      GREEN_TAO_DENSE_COUNT :
        !k delta. 2 <= k /\ &0 < delta
          ==> ?c X0. &0 < c /\
                     !A X. A SUBSET {p | prime p} /\ X0 <= X /\
                           delta * &(CARD {p | prime p /\ p <= X}) <=
                           &(CARD {p | p IN A /\ p <= X})
                           ==> c * &X pow 2 / log(&X) pow k <=
                               &(CARD {(a,d) | 0 < d /\ a + (k - 1) * d <= X /\
                                               !j. j < k ==> a + j * d IN A})

  and `GREEN_TAO_DENSE`, `GREEN_TAO_DENSE_INFINITE`, `GREEN_TAO_COUNT`.
  The three ingredients: a majorant based on optimal Selberg
  weights and its linear forms condition (`gt_majorant.ml`, on
  `lf_*.ml`); Zhao's transference, with the dense model theorem by
  multiplicative weights and the counting lemma of Conlon, Fox and Zhao
  (`gt_dense_model.ml`, `gt_hypergraph.ml`, `gt_counting.ml`,
  `gt_transfer.ml`), giving the relative Szemeredi theorem
  `RELATIVE_SZEMEREDI`; and Szemeredi's theorem in Z_N, `WEIGHTED_SZEMEREDI`
  of `Library/szemeredi.ml`.  The separate `gt_density.ml` gives
  `GT_DENSITY`, a density estimate in the fixed residue class 1 modulo W
  using Siegel-Walfisz; the dense-subset proof uses the prime number
  theorem and residue pigeonholing for its density.

## Files

| Files | Contents |
| --- | --- |
| `base.ml` | the libraries below (see Loading) |
| `nt.ml`, `sums.ml`, `primes.ml` | elementary facts, partial summation in integral form, Mertens' second theorem with an error term |
| `dseries.ml`, `characters.ml`, `lfun.ml`, `perron.ml`, `siegel.ml`, `zerofree.ml`, `vaughan.ml`, `sw.ml`, `gauss.ml`, `largesieve.ml`, `bilinear.ml`, `bv.ml` | Dirichlet series and characters, Perron's formula, Siegel, the zero-free region, Siegel-Walfisz, the large sieve, Bombieri-Vinogradov |
| `sieve.ml`, `dde.ml`, `linear.ml`, `jurkat.ml`, `selberg.ml`, `pairs_sieve.ml`, `brun.ml`, `goldbach_shnirelman.ml` | the sieve framework |
| `chen_sieve.ml`, `chen_lower.ml`, `chen_aq.ml`, `chen_weights.ml`, `chen_main.ml`, `chen_sb.ml`, `chen.ml`, `chen_shift.ml`, `chen_distinct.ml` | Chen's theorem |
| `pnt_ap.ml`, `brun_titchmarsh.ml`, `erdos_covering.ml`, `romanov.ml`, `titchmarsh.ml`, `hardy_ramanujan.ml` | the classical corollaries |
| `bg_s1.ml`, `bg_s2.ml`, `bg_weights.ml`, `bg_dyadic.ml`, `bg_assembly.ml`, `bounded_gaps.ml` | bounded gaps and Maynard-Tao |
| `pnt_error.ml`, `sw_theta.ml`, `expsum.ml`, `vinogradov_minor.ml`, `vinogradov.ml`, `goldbach_almost.ml` | Vinogradov's three primes theorem, Goldbach for almost all even numbers |
| `waring_weyl.ml`, `waring_major.ml`, `waring_singular.ml`, `waring.ml` | Waring's problem |
| `linnik.ml`, `bdh.ml` | Linnik, Barban-Davenport-Halberstam |
| `hua_minor.ml`, `hua_major.ml`, `hua_singular.ml`, `hua.ml` | Hua's five prime squares |
| `square_plus_one.ml`, `square_plus_one_p3.ml` | n^2 + 1 |
| `van_der_corput.ml` | three-term progressions of primes |
| `lf_local.ml`, `lf_selberg.ml`, `lf_estimate.ml`, `gt_majorant.ml` | the Green-Tao majorant |
| `gt_density.ml` | a density estimate for W-tricked primes in a fixed residue class |
| `gt_dense_model.ml`, `gt_hypergraph.ml`, `gt_counting.ml`, `gt_transfer.ml` | the transference and the relative Szemeredi theorem |
| `gt_green_tao.ml` | the Green-Tao theorem |

Every file starts with a banner describing its results and methods and
lists the files it needs.  Most topic-specific constants carry prefixes
(`sieve_`, `rosser_`, `selberg_`, `chen_`, `maynard_` and `col_` for
Maynard's sieve, `bv_`, `waring_`, `hua_`, `goldbach_`, `lf_` for linear
forms, `zn_` for Z_N in the transference).  General number-theoretic notions
such as `almost_prime`, `primitive_character` and `dseries` use descriptive
names without a topic prefix.

## Loading

Every load uses a `Sieve/<file>` path, so the directory containing `Sieve`
must be on HOL Light's load path: install `Sieve` under the HOL Light root
or start HOL Light in the directory containing it.  Then, with
`ulimit -s unlimited`:

    loadt "Sieve/make.ml";;

`base.ml` loads the libraries the directory builds on:
`Multivariate/cauchy.ml`, `Library/multiplicative.ml`, `100/pnt.ml`,
`100/dirichlet.ml`, `Examples/schnirelmann.ml` and `Library/szemeredi.ml`
(which loads `100/bertrand.ml`).  This needs HOL Light of 5 November 2026
(commit 56aa2a8) or later, the first with `Library/szemeredi.ml`.  From a
fresh HOL Light the whole load takes about 40 minutes of CPU: 26 for the
libraries, most of them in `Multivariate/cauchy.ml`, and 10 for the files
of `Sieve/`.  Timing depends on the machine and OCaml build.
Any file can be loaded on its own with its prerequisites, e.g.
`needs "Sieve/vinogradov.ml";;`.

The files are written for the parse priorities left by
`Multivariate/cauchy.ml`, in which the arithmetic operators default to
complex, then real, then num; each development file sets them after its
`needs` lines (`prioritize_num(); prioritize_complex();;`), so it parses
the same whatever was loaded or prioritized before it.  For strict
checking of the Sieve quotations, load the standard prerequisites before
setting `type_invention_error`:

    use_file_raise_failure := true;;
    needs "Sieve/base.ml";;
    type_invention_error := true;;
    loadt "Sieve/make.ml";;

## Sources

The banners cite the sources by chapter, section and theorem number, [N]
being Nathanson and [D] Davenport:

- M. B. Nathanson, *Additive Number Theory: The Classical Bases*, GTM 164,
  Springer 1996: the sieve framework and Chen's theorem, Romanov,
  Vinogradov's three primes theorem, Waring's problem.
- H. Davenport, *Multiplicative Number Theory*, 3rd edition, GTM 74,
  Springer 2000: Siegel's theorem, Vaughan's identity,
  Barban-Davenport-Halberstam.
- J. Maynard, Small gaps between primes, Annals of Mathematics 181 (2015).
- B. Green and T. Tao, The primes contain arbitrarily long arithmetic
  progressions, Annals of Mathematics 167 (2008).
- D. Conlon, J. Fox and Y. Zhao, A relative Szemeredi theorem, GAFA 25
  (2015); Y. Zhao, An arithmetic transference proof of a relative
  Szemeredi theorem, Math. Proc. Cambridge Philos. Soc. 156 (2014).
- O. Reingold, L. Trevisan, M. Tulsiani and S. Vadhan, Dense subsets of
  pseudorandom sets, FOCS 2008 (the dense model theorem by multiplicative
  weights).

Also consulted: H. Halberstam and H.-E. Richert, *Sieve Methods*,
Academic Press 1974; H. Iwaniec and E. Kowalski, *Analytic Number
Theory*, AMS 2004; J. Friedlander and H. Iwaniec, *Opera de Cribro*, AMS
2010.
