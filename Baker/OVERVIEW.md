# Linear forms in logarithms and their applications in HOL Light

This is the detailed guide to the directory Baker/ of the HOL Light tree;
Baker/README is the summary. The 131 files of the directory (about 95,000
lines) formalize the theory of linear forms in the logarithms of algebraic
numbers of A. Baker and its applications: the Baker-Feldman bound and the
qualitative theorem of Baker, Sharpening I for algebraic numbers and for
algebraic coefficients, Tijdeman on the Catalan equation, explicit bounds
for two logarithms, Thue, Mordell, superelliptic and hyperelliptic
equations and integral points on elliptic curves, the Schinzel-Tijdeman
theorem, prime factors of polynomial values, perfect powers in Lucas
sequences, the imaginary quadratic fields of class number one and two, and
unique factorization in imaginary quadratic fields. They build on the
algebraic number theory library ANT/ (Part XI) and on the library files of
the tree. The parts below state the main results; the file map at the end
lists the files by the sections of Baker/make.ml.

Statements below are printed by HOL Light after loadt "Baker/make.ml" (HOL
printer syntax: `forall`, `exists`, `&n` for the real number n, `Cx` for
the embedding of R into C).

## Building

From the root of the HOL Light tree, in a fresh session:

    loadt "Baker/make.ml";;          (* everything *)
    needs "Baker/theorem.ml";;       (* one file with its prerequisites *)
    loadt "Baker/make_core.ml";;     (* sections 1 to 4 *)
    loadt "Baker/make_twolog.ml";;   (* sections 1 and 9 *)
    loadt "Baker/make_laurent.ml";;  (* sections 1, 9 and 10 *)

Every file starts with needs lines for the library files, the files of ANT/
and the files of Baker/ whose results it uses, followed by
prioritize_real();; prioritize_num();; so that it parses in the same way
whatever was loaded before it; needs "Baker/x.ml" loads one file with all
it needs. Baker/make.ml first loads the library prerequisites in an order in
which they load together (Library/jacobi.ml before the Multivariate files,
100/dirichlet.ml before Multivariate/gamma.ml): Library/jacobi.ml,
100/transcendence.ml, Examples/mangoldt.ml, 100/dirichlet.ml,
Multivariate/gamma.ml and Examples/gcdrecurrence.ml; then the files of the
directory in the 22 sections of the file map below. The ANT files load
through the needs lines of the files that use them (57 of the 91 files of
ANT/).

The partial loaders load sections 1 to 4 (the Baker core, BAKER_FELDMAN and
its applications), sections 1 and 9 (two logarithms and the Steiner
theorem) and sections 1, 9 and 10 (the Laurent bound for rationals); of the
library they need only 100/transcendence.ml, Examples/mangoldt.ml and the
files these load (and 100/sqrt.ml for Baker/apps.ml).

Load times from a fresh hol.ml, as holtest runs a test: Baker/make.ml about
70 minutes (about 55 for hol.ml and the library prerequisites, about 15 for
the files of ANT/ and of Baker/ with the library files they need); the
partial loaders Baker/make_core.ml about 55 minutes, Baker/make_twolog.ml
about 54 and Baker/make_laurent.ml about 54, almost all of it for their
library prerequisites. In a session in which the library prerequisites of
Baker/make.ml are loaded, loadt "Baker/make.ml" takes about 15 minutes.

## Main results

## Part I. Linear forms in logarithms (Baker 1966-1975)

### BAKER_FELDMAN  (Baker/theorem.ml)
The effective Baker-Feldman lower bound (Baker, Transcendental Number Theory, Thm 3.1): a non-zero linear form in logarithms of algebraic numbers with algebraic coefficients of height at most B is at least B^-C.

```
|- forall n lg Dx.
       (forall r. r IN 1..n ==> algebraic_number (cexp (lg r)))
       ==> (exists C.
                forall B beta db ab.
                    &2 <= B /\
                    (forall j.
                         j <= n
                         ==> 1 <= db j /\
                             db j <= Dx /\
                             (forall i.
                                  integer (ab j i) /\ abs (ab j i) <= B) /\
                             ~(ab j (db j) = &0) /\
                             vsum (0..db j) (\i. Cx (ab j i) * beta j pow i) =
                             Cx (&0)) /\
                    ~(beta 0 + vsum (1..n) (\r. beta r * lg r) = Cx (&0))
                    ==> inv (B pow C) <=
                        norm (beta 0 + vsum (1..n) (\r. beta r * lg r)))
```

### BAKER_LINEAR_INDEPENDENCE  (Baker/apps.ml)
Baker's qualitative theorem: logarithms of algebraic numbers that are linearly independent over Q are linearly independent over the algebraic numbers, together with 1.

```
|- forall n lg beta.
       1 <= n /\
       (forall r. r IN 1..n ==> algebraic_number (cexp (lg r))) /\
       (forall b.
            (forall r. r IN 1..n ==> integer (b r)) /\
            vsum (1..n) (\r. Cx (b r) * lg r) = Cx (&0)
            ==> (forall r. r IN 1..n ==> b r = &0)) /\
       (forall j. j <= n ==> algebraic_number (beta j)) /\
       beta 0 + vsum (1..n) (\r. beta r * lg r) = Cx (&0)
       ==> (forall j. j <= n ==> beta j = Cx (&0))
```

### BAKER_INHOMOGENEOUS  (Baker/apps.ml)
The inhomogeneous form.

```
|- forall n lg beta.
       (forall r. r IN 1..n ==> algebraic_number (cexp (lg r))) /\
       (forall j. j <= n ==> algebraic_number (beta j)) /\
       beta 0 + vsum (1..n) (\r. beta r * lg r) = Cx (&0)
       ==> beta 0 = Cx (&0)
```

### GELFOND_SCHNEIDER  (Baker/apps.ml)
Gelfond-Schneider as a corollary.

```
|- forall l beta.
       algebraic_number (cexp l) /\
       ~(l = Cx (&0)) /\
       algebraic_number beta /\
       ~(exists q. rational q /\ beta = Cx q)
       ==> ~algebraic_number (cexp (beta * l))
```

### EXP_PI_TRANSCENDENTAL  (Baker/apps.ml)
e^pi is transcendental.

```
|- ~algebraic_number (cexp (Cx pi))
```

### SUNIT_GAP  (Baker/apps.ml)
Gaps between S-units (Tijdeman).

```
|- forall S.
       FINITE S /\ (forall p. p IN S ==> prime p)
       ==> (exists c C.
                &0 < c /\
                (forall x y.
                     3 <= x /\
                     x < y /\
                     (forall p. prime p /\ p divides x ==> p IN S) /\
                     (forall p. prime p /\ p divides y ==> p IN S)
                     ==> c * &x / log (&x) pow C <= &y - &x))
```

### PI_IRRATIONALITY_MEASURE  (Baker/apps.ml)
An irrationality measure for pi.

```
|- exists c C.
       &0 < c /\
       (forall p q.
            integer p /\ integer q /\ &1 <= q
            ==> c / q pow C <= abs (pi - p / q))
```

### BAKER_UNIFORM_RATIONAL  (Baker/uniform.ml)
A uniform lower bound for arbitrary (possibly dependent) logarithms of rationals.

```
|- forall n.
       exists c kappa.
           forall u v b B g0.
               &1 <= g0 /\
               &2 <= B /\
               (forall r.
                    r IN 1..n
                    ==> 1 <= u r /\
                        1 <= v r /\
                        &(u r) <= exp g0 /\
                        &(v r) <= exp g0) /\
               (forall r. r IN 1..n ==> integer (b r) /\ abs (b r) <= B) /\
               ~(sum (1..n) (\r. b r * log (&(u r) / &(v r))) = &0)
               ==> exp (--(c * g0 pow kappa * log B)) <=
                   abs (sum (1..n) (\r. b r * log (&(u r) / &(v r))))
```

Further applications (Baker/apps_examples.ml): transcendence of log2 3, e^(pi sqrt 163), i^i, 2^sqrt2 3^sqrt3, sin/cos/tan/atn of algebraic numbers (Lindemann), integrals such as the integral of 1/(1+x^3) over [0,1]; Pillai's equation a^m - b^n = k has finitely many solutions; Stormer: consecutive smooth numbers are bounded; irrationality measures for log 2 / log 3.

## Part II. Sharpening I (Baker 1972), Tijdeman's theorem and the Catalan exponents

Baker, A sharpening of the bounds for linear forms in logarithms I (Acta
Arith. 21, 1972), for algebraic numbers and uniform in the data: for
non-zero algebraic numbers al_1, ..., al_n of degree at most d, roots of
integer polynomials of height at most exp g0 (r < n) and A (r = n),
principal logarithms and integer coefficients of size at most B, the linear
form Lambda is 0 or |Lambda| >= exp(-C g0^K log A log B), C and K depending
only on n and d (BAKER_SHARPENING; the real form BAKER_SHARPENING_REAL).
With algebraic coefficients bt_1, ..., bt_n of degree at most d, roots of
integer polynomials of height at most B (Baker, A central theorem in
transcendence theory, in Diophantine Approximation and Its Applications,
ed. Osgood, 1973, and Transcendental Number Theory, p. 23), the form
Lambda = sum bt_r log al_r is 0 or |Lambda| >=
exp(-C g0^K log A log(B log A)) (BAKER_SHARPENING_ALGEBRAIC_COEFFS; the
real form SHARPC_SHARPENING_REAL). For a fixed number field the form
SHARP_BAKER_NUMBER_FIELD (fixed numbers and one variable number with
denominator and conjugates at most A) gives the Schinzel-Tijdeman theorem
(Part XIII). Tijdeman's Theorem 2 for rationals
(TIJDEMAN_LINEAR_FORMS_RATIONAL) is the case d = 1, and with it the
exponents of the Catalan equation are bounded (CATALAN_EXPONENT_BOUND; Ko
Chao and Catalan finiteness are in Part IV). The class number two problem
(Part XV) uses the algebraic coefficients with n = 3, d = 2.

One machinery, two endings. Both bounds come from one machinery with
complex coefficients bb r (Baker/make.ml section 6); integer coefficients b
r are the case bb r = Cx(b r), coefficient data of degree 1 (b r is the root
of X - b r, SHARPC_COEFDATA_INTEGER). The machinery: the auxiliary function
with Delta-function factors at the nodes x_r = bb_n mu_r - bb_r mu_n; Kummer
theory over any subfield of C (KUMMER_COMPLEX); Lemmas 5, 6 and 8 by the
field-free Siegel and Liouville lemmas of the Baker core over the 2n
algebraic numbers (alphas, betas), each proved once for a Delta
representation (sharp_deltarep below: an integer polynomial in the alphas
and the betas equal to a multiplier M m times the Delta product, of degree E
s in the betas and coefficient size W s, s = m 1 + ... + m (n - 1); the
bound functions sharp_psize, sharp_liou5 and sharp_lb8 depend on W, E and
the multiplier bound Mb); section 4 over Q(alphas, betas) (rational betas do
not change the field, COMPLEX_SUBFIELD_GENERATED_UNION_RATIONAL); the
extrapolation and one parametric core (SHARP_CORE_PARAMETRIC); the numeric
design (SHARP_CORE_DESIGN, the design facts of both endings) with the
extrapolation radius Q^(8 c), c growing with the degrees (the radius Q^8 of
rational data does not absorb the Liouville loss once the product of the
degrees is at least 4); number field tools (denominators of p-th roots by
the ideal norms of ANT/, Baker and Stark 1971, Lemma 4; an element with
bounded denominator and conjugates is a root of an integer polynomial of
controlled height); the uniform base BAKER_UNIFORM_ALGCOEFF (exp(-c Mb^kappa
log B) for algebraic coefficients, by induction on n from the uniform core
BAKER_CORE_UNIFORM_ALGCOEFF of Baker/uniform.ml (section 4), which
applies BAKER_CORE_UNIFORM with the betas as n extra algebraic numbers), in
place of the pigeonhole ending of Baker 1973, which is not uniform in the
data; and the descent tools with -1 as a fixed number. No Weil height is
needed.

Integer coefficients (Baker/make.ml section 6). Delta(x; m) is an integer at
an integer node, of size at most (4B+2)^m 2^L for |x| <= 2BL by the Baker
binomial trick (SHARP_DELTAREP_INT: multiplier 1, degree 0 in the betas), so
at this instance the bound functions are those of Sharpening I; the numeric
ending with c = D^n, the analytic size B and h = ceil(log(4B+2)) gives log A
log B (SHARP_CORE_ALGEBRAIC); the descent runs in Q(alphas) with integer
coefficients, with a Liouville case for small B and the base case
SHARP_UNIFORM_ALG, the instance of SHARPC_UNIFORM_ALG with integer
coefficients (SHARP_BAKER_ALGEBRAIC).

Algebraic coefficients (Baker/make.ml section 7), and where log(B log A)
comes from. Here m! Delta(x; m) = (x + 1) ... (x + m) is an integer
polynomial in the betas (SHARP_DELTAREP_ALG: multiplier prod_r
m_r! <= S0^S0, degree s, size (2 Lm + s)^s; Baker 1973). The numeric layer
absorbs these factorials and the heights of the betas by one extra power of
the Liouville term (radius exponent c = 2 D^(2n), modified degree data), so
the shared design applies with the analytic size Bp = (2 Lm + S0) (1 + D)^n
B^(3n) in place of B. Since Lm and S0 are about log A times a power of Q
(Q = 2^e ceil(g0)), h = ceil(log(4 Bp + 2)) is about 3n log B + log log
A + O(log g0), and the final inequality 17 h gN Q^M <= C g0^(M+1) log A
log(B log A) (SHARPC_NUM_FINAL_INEQ) gives SHARPC_CORE. So the extra log log
A comes from the arithmetic of algebraic coefficients, not from the numeric
design (the same for both endings) nor from the descent (which preserves the
shape). The descent normalises bb n = 1 (the quotients bb r / bb n have
degree at most d^(2n)), stays in the fixed field Q(alphas, betas) with the
new coefficients (bb r + j_r) / p (Baker: (beta_r - j_r) / p), needs no
small-B case and ends in SHARPC_UNIFORM_ALG (SHARPC_BAKER).

Baker/make.ml sections 4 (the uniform bounds and the uniform core), 5
(algebraic integers and number fields inside C), 6 (Sharpening I: the
machinery and the integer ending), 7 (the algebraic ending) and 8
(Tijdeman and the Catalan exponents).

### BAKER_SHARPENING  (Baker/sharp_main.ml)
Baker 1972 for algebraic numbers: heights of integer polynomials vanishing at the al r, principal logarithms; C and K depend only on n and the degree bound d.

```
|- forall n d.
       1 <= n
       ==> (exists C K.
                forall al a dd bb A B g0.
                    &1 <= g0 /\
                    exp (&1) <= A /\
                    &2 <= B /\
                    (forall r.
                         r IN 1..n
                         ==> ~(al r = Cx (&0)) /\
                             1 <= dd r /\
                             dd r <= d /\
                             (forall j. integer (a r j)) /\
                             ~(a r (dd r) = &0) /\
                             vsum (0..dd r) (\j. Cx (a r j) * al r pow j) =
                             Cx (&0) /\
                             integer (bb r) /\
                             abs (bb r) <= B) /\
                    (forall r j. r IN 1..n - 1 ==> abs (a r j) <= exp g0) /\
                    (forall j. abs (a n j) <= A) /\
                    ~(vsum (1..n) (\r. Cx (bb r) * clog (al r)) = Cx (&0))
                    ==> exp (--(C * g0 pow K * log A * log B)) <=
                        norm (vsum (1..n) (\r. Cx (bb r) * clog (al r))))
```

### BAKER_SHARPENING_REAL  (Baker/sharp_main.ml)
The real form: positive real algebraic numbers and real logarithms.

```
|- forall n d.
       1 <= n
       ==> (exists C K.
                forall x a dd bb A B g0.
                    &1 <= g0 /\
                    exp (&1) <= A /\
                    &2 <= B /\
                    (forall r.
                         r IN 1..n
                         ==> &0 < x r /\
                             1 <= dd r /\
                             dd r <= d /\
                             (forall j. integer (a r j)) /\
                             ~(a r (dd r) = &0) /\
                             sum (0..dd r) (\j. a r j * x r pow j) = &0 /\
                             integer (bb r) /\
                             abs (bb r) <= B) /\
                    (forall r j. r IN 1..n - 1 ==> abs (a r j) <= exp g0) /\
                    (forall j. abs (a n j) <= A) /\
                    ~(sum (1..n) (\r. bb r * log (x r)) = &0)
                    ==> exp (--(C * g0 pow K * log A * log B)) <=
                        abs (sum (1..n) (\r. bb r * log (x r))))
```

### BAKER_SHARPENING_ALGEBRAIC_COEFFS  (Baker/sharpc_main.ml)
Baker 1973 (TNT p. 23), uniform in the data: algebraic coefficients bt r of degree at most d and height at most B, principal logarithms; C and K depend only on n and d.

```
|- forall n d.
       1 <= n
       ==> (exists C K.
                forall al a dd bt ab db A B g0.
                    &1 <= g0 /\
                    exp (&1) <= A /\
                    &2 <= B /\
                    (forall r.
                         r IN 1..n
                         ==> ~(al r = Cx (&0)) /\
                             1 <= dd r /\
                             dd r <= d /\
                             (forall j. integer (a r j)) /\
                             ~(a r (dd r) = &0) /\
                             vsum (0..dd r) (\j. Cx (a r j) * al r pow j) =
                             Cx (&0) /\
                             1 <= db r /\
                             db r <= d /\
                             (forall j.
                                  integer (ab r j) /\ abs (ab r j) <= B) /\
                             ~(ab r (db r) = &0) /\
                             vsum (0..db r) (\j. Cx (ab r j) * bt r pow j) =
                             Cx (&0)) /\
                    (forall r j. r IN 1..n - 1 ==> abs (a r j) <= exp g0) /\
                    (forall j. abs (a n j) <= A) /\
                    ~(vsum (1..n) (\r. bt r * clog (al r)) = Cx (&0))
                    ==> exp (--(C * g0 pow K * log A * log (B * log A))) <=
                        norm (vsum (1..n) (\r. bt r * clog (al r))))
```

### SHARPC_SHARPENING_REAL  (Baker/sharpc_main.ml)
The real form: positive real algebraic numbers, real algebraic coefficients and real logarithms.

```
|- forall n d.
       1 <= n
       ==> (exists C K.
                forall x a dd bt ab db A B g0.
                    &1 <= g0 /\
                    exp (&1) <= A /\
                    &2 <= B /\
                    (forall r.
                         r IN 1..n
                         ==> &0 < x r /\
                             1 <= dd r /\
                             dd r <= d /\
                             (forall j. integer (a r j)) /\
                             ~(a r (dd r) = &0) /\
                             sum (0..dd r) (\j. a r j * x r pow j) = &0 /\
                             1 <= db r /\
                             db r <= d /\
                             (forall j.
                                  integer (ab r j) /\ abs (ab r j) <= B) /\
                             ~(ab r (db r) = &0) /\
                             sum (0..db r) (\j. ab r j * bt r pow j) = &0) /\
                    (forall r j. r IN 1..n - 1 ==> abs (a r j) <= exp g0) /\
                    (forall j. abs (a n j) <= A) /\
                    ~(sum (1..n) (\r. bt r * log (x r)) = &0)
                    ==> exp (--(C * g0 pow K * log A * log (B * log A))) <=
                        abs (sum (1..n) (\r. bt r * log (x r))))
```

### BAKER_UNIFORM_ALGCOEFF  (Baker/sharp_uniform.ml)
The uniform base of both endings: a uniform Baker bound exp(-c Mb^kappa log B) for algebraic coefficients of degree at most Dx and height at most B, with the data of baker_logdata (no independence hypothesis on the logarithms).

```
|- forall n Dmax Dx.
       1 <= Dmax /\ 1 <= Dx
       ==> (exists c kappa.
                forall Mb lg a d H bb ab db B.
                    &1 <= Mb /\
                    &2 <= B /\
                    baker_logdata n lg a d H Mb Dmax /\
                    sharpc_coefdata n bb ab db B /\
                    (forall r. r IN 1..n ==> db r <= Dx) /\
                    ~(vsum (1..n) (\r. bb r * lg r) = Cx (&0))
                    ==> exp (--(c * Mb pow kappa * log B)) <=
                        norm (vsum (1..n) (\r. bb r * lg r)))
```

### SHARPC_BAKER  (Baker/sharpc_descent.ml)
The form proved by the descent, with the two definitions below.

```
|- forall n d. 1 <= n ==> (exists C K. sharpc_bound_property n d C K)
```

### sharpc_coefdata  (Baker/uniform.ml)
The classical height data of the coefficients: bb r is a root of the integer polynomial ab r of degree db r and height at most Hb (Baker/make.ml section 4; integer coefficients b r are the data of degree 1 with bb r = Cx(b r), SHARPC_COEFDATA_INTEGER).

```
|- forall n Hb db ab bb.
       sharpc_coefdata n bb ab db Hb <=>
       (forall r.
            r IN 1..n
            ==> 1 <= db r /\
                (forall j. integer (ab r j) /\ abs (ab r j) <= Hb) /\
                ~(ab r (db r) = &0) /\
                vsum (0..db r) (\j. Cx (ab r j) * bb r pow j) = Cx (&0))
```

### sharpc_bound_property  (Baker/sharp_defs.ml)
Sharpening I with algebraic coefficients for n logarithms of algebraic numbers of degree at most d.

```
|- forall d C K n.
       sharpc_bound_property n d C K <=>
       (forall lg a dd bb ab db A B g0.
            &1 <= g0 /\
            exp (&1) <= A /\
            &2 <= B /\
            sharp_algdata n lg a dd (\r. if r = n then A else exp g0) /\
            sharpc_coefdata n bb ab db B /\
            (forall r.
                 r IN 1..n
                 ==> dd r <= d /\
                     db r <= d /\
                     --pi < Im (lg r) /\
                     Im (lg r) <= pi) /\
            ~(vsum (1..n) (\r. bb r * lg r) = Cx (&0))
            ==> exp (--(C * g0 pow K * log A * log (B * log A))) <=
                norm (vsum (1..n) (\r. bb r * lg r)))
```

### SHARPC_CORE  (Baker/sharpc_num.ml)
The core: a tiny normalised linear form (bb n = 1) forces a Kummer relation for the last number with a prime 4 D^2 <= pr <= cB g0^K and g in the field of the alphas and betas (sharpc_core_property of Baker/sharp_defs.ml).

```
|- forall n D.
       1 <= n /\ 1 <= D
       ==> (exists C K cB.
                &0 <= C /\ &1 <= cB /\ sharpc_core_property n D C K cB)
```

### SHARPC_UNIFORM_ALG  (Baker/sharp_uniform.ml)
The base bound in classical heights: principal logarithms of algebraic numbers of height at most exp G, exp(-c G^k log B); its instance with integer coefficients, SHARP_UNIFORM_ALG, is the base case of the descent for integer coefficients.

```
|- forall m D.
       1 <= D
       ==> (exists c k.
                forall lg a dd H bb ab db B G.
                    &1 <= G /\
                    &2 <= B /\
                    sharp_algdata m lg a dd H /\
                    sharpc_coefdata m bb ab db B /\
                    (forall r.
                         r IN 1..m
                         ==> dd r <= D /\
                             db r <= D /\
                             H r <= exp G /\
                             --pi < Im (lg r) /\
                             Im (lg r) <= pi) /\
                    ~(vsum (1..m) (\r. bb r * lg r) = Cx (&0))
                    ==> exp (--(c * G pow k * log B)) <=
                        norm (vsum (1..m) (\r. bb r * lg r)))
```

### SHARP_BAKER_NUMBER_FIELD  (Baker/sharp_main.ml)
Fixed non-zero numbers al j of the number field generated by a finite set s of algebraic numbers and one variable number x of it with an integer denominator den <= A and all conjugates of modulus at most A: the form used for Schinzel-Tijdeman.

```
|- forall s N al.
       FINITE s /\
       (forall z. z IN s ==> algebraic_number z) /\
       (forall j.
            j IN 1..N
            ==> al j IN ring_carrier (subfield_generated complex_ring s) /\
                ~(al j = Cx (&0)))
       ==> (exists C.
                forall x den bb b A B.
                    x IN ring_carrier (subfield_generated complex_ring s) /\
                    ~(x = Cx (&0)) /\
                    integer den /\
                    &1 <= den /\
                    den <= A /\
                    algebraic_integer (Cx den * x) /\
                    (forall g.
                         g IN
                         complex_embeddings
                         (subfield_generated complex_ring s)
                         ==> norm (g x) <= A) /\
                    exp (&1) <= A /\
                    &2 <= B /\
                    (forall j.
                         j IN 1..N ==> integer (bb j) /\ abs (bb j) <= B) /\
                    integer b /\
                    abs b <= B /\
                    ~(vsum (1..N) (\j. Cx (bb j) * clog (al j)) +
                      Cx b * clog x =
                      Cx (&0))
                    ==> exp (--(C * log A * log B)) <=
                        norm
                        (vsum (1..N) (\j. Cx (bb j) * clog (al j)) +
                         Cx b * clog x))
```

### SHARP_BAKER_ALGEBRAIC  (Baker/sharp_descent.ml)
The form proved by the descent, with the two definitions below (complex logarithms lg r with imaginary part in (-pi, pi] of roots of integer polynomials).

```
|- forall n d. 1 <= n ==> (exists C K. sharp_bound_property_alg n d C K)
```

### sharp_algdata  (Baker/sharp_defs.ml)
The classical height data: cexp(lg r) is a root of the integer polynomial a r of degree dd r and height at most H r.

```
|- forall n H dd a lg.
       sharp_algdata n lg a dd H <=>
       (forall r.
            r IN 1..n
            ==> 1 <= dd r /\
                &1 <= H r /\
                (forall j. integer (a r j) /\ abs (a r j) <= H r) /\
                ~(a r (dd r) = &0) /\
                vsum (0..dd r) (\j. Cx (a r j) * cexp (lg r) pow j) = Cx (&0))
```

### sharp_bound_property_alg  (Baker/sharp_defs.ml)
Sharpening I for n logarithms of algebraic numbers of degree at most d.

```
|- forall d C K n.
       sharp_bound_property_alg n d C K <=>
       (forall lg a dd bb A B g0.
            &1 <= g0 /\
            exp (&1) <= A /\
            &2 <= B /\
            sharp_algdata n lg a dd (\r. if r = n then A else exp g0) /\
            (forall r.
                 r IN 1..n
                 ==> dd r <= d /\
                     --pi < Im (lg r) /\
                     Im (lg r) <= pi /\
                     integer (bb r) /\
                     abs (bb r) <= B) /\
            ~(vsum (1..n) (\r. Cx (bb r) * lg r) = Cx (&0))
            ==> exp (--(C * g0 pow K * log A * log B)) <=
                norm (vsum (1..n) (\r. Cx (bb r) * lg r)))
```

### sharp_deltarep  (Baker/sharp_defs.ml)
The Delta representation of the one machinery: for every vector m of derivative orders, M m times the Delta product of every index mu with mu r <= Lm is an integer polynomial over the 2n numbers (at k <= n the alphas, of degree 0; at n + r the coefficient bb r, of degree E s), with coefficient sum at most W s, s = m 1 + ... + m (n - 1); W, E and the bound Mb of M are monotone. Instances: SHARP_DELTAREP_INT (integer coefficients: M = 1, E = 0, W s = (4B+2)^s 2^((n-1)Lm)) and SHARP_DELTAREP_ALG (algebraic coefficients: M m = prod m_r!, E s = s, W s = (2Lm+s)^s, Mb s = s^s).

```
|- forall Mb Lm E W M n bb.
       sharp_deltarep n bb Lm W E Mb M <=>
       (forall s t. s <= t ==> W s <= W t /\ E s <= E t /\ Mb s <= Mb t) /\
       (forall m.
            1 <= M m /\
            &(M m) <= Mb (nsum (1..n - 1) m) /\
            (forall mu.
                 (forall r. r IN 1..n ==> mu r <= Lm)
                 ==> (exists g.
                          intpoly (1..n + n)
                          (\k. if k <= n then 0 else E (nsum (1..n - 1) m))
                          (W (nsum (1..n - 1) m))
                          g /\
                          (forall x.
                               (forall r. r IN 1..n ==> x (n + r) = bb r)
                               ==> g x =
                                   Cx (&(M m)) *
                                   cproduct (1..n - 1)
                                   (\r.
                                        feldman_delta (m r)
                                        (sharp_x n bb mu r))))))
```

### KUMMER_COMPLEX  (Baker/kummer.ml)
Kummer theory over any subfield s of C: if 1, w0, ..., w0^(p-1) are linearly dependent over the s-algebra generated by p-th roots w r of numbers al r of s, then al0 is a product of powers of the al r times a p-th power in s.

```
|- forall p s al w m al0 w0 E.
       prime p /\
       s subfield_of complex_ring /\
       (forall r.
            1 <= r /\ r <= m
            ==> al r IN s /\ ~(al r = Cx (&0)) /\ w r pow p = al r) /\
       al0 IN s /\
       ~(al0 = Cx (&0)) /\
       w0 pow p = al0 /\
       (forall j.
            j < p
            ==> E j IN
                ring_carrier
                (subring_generated complex_ring (s UNION IMAGE w (1..m)))) /\
       vsum (0..p - 1) (\j. E j * w0 pow j) = Cx (&0) /\
       ~(forall j. j < p ==> E j = Cx (&0))
       ==> (exists jj g.
                (forall r. jj r < p) /\
                g IN s /\
                al0 = cproduct (1..m) (\r. al r pow jj r) * g pow p)
```

### TIJDEMAN_LINEAR_FORMS_RATIONAL  (Baker/tijdeman.ml)
Tijdeman (1976), Theorem 2, for rationals: Baker's Sharpening I with the dependence log A log B, the case d = 1 of BAKER_SHARPENING_REAL (u / v is the root of v X - u). The formal proof repairs a gap in Sharpening I (the denominator of Lemma 8 costs h log h; replaced by a common multiple of 1..N, as Tijdeman's Lemma T1 intends; the one Lemma 8 of the machinery does the same for both endings).

```
|- forall n.
       1 <= n
       ==> (exists C K.
                forall u v bb A B g0.
                    &1 <= g0 /\
                    exp (&1) <= A /\
                    &2 <= B /\
                    (forall r.
                         r IN 1..n
                         ==> 1 <= u r /\
                             1 <= v r /\
                             integer (bb r) /\
                             abs (bb r) <= B) /\
                    (forall r.
                         r IN 1..n - 1
                         ==> &(u r) <= exp g0 /\ &(v r) <= exp g0) /\
                    &(u n) <= A /\
                    &(v n) <= A /\
                    ~(sum (1..n) (\r. bb r * log (&(u r) / &(v r))) = &0)
                    ==> exp (--(C * g0 pow K * log A * log B)) <=
                        abs (sum (1..n) (\r. bb r * log (&(u r) / &(v r)))))
```

### CATALAN_EXPONENT_BOUND  (Baker/tijdeman.ml)
The exponents of the Catalan equation are bounded (Tijdeman, section 5).

```
|- exists M.
       forall p q x y.
           prime p /\
           prime q /\
           ODD p /\
           ODD q /\
           ~(p = q) /\
           2 <= x /\
           2 <= y /\
           x EXP p = y EXP q + 1
           ==> p <= M /\ q <= M
```

## Part III. An explicit lower bound for two logarithms; Steiner's theorem

### TWOLOG_RATIONAL  (Baker/twolog.ml)
Explicit bound for two logarithms of rationals by interpolation determinants (Laurent; following Bugeaud, Linear Forms in Logarithms and Applications, Ch. 11).

```
|- forall p1 q1 p2 q2 b1 b2 h1 h2.
       1 <= p1 /\
       1 <= q1 /\
       1 <= p2 /\
       1 <= q2 /\
       1 <= b1 /\
       1 <= b2 /\
       &1 <= h1 /\
       log (&p1) <= h1 /\
       log (&q1) <= h1 /\
       &1 <= h2 /\
       log (&p2) <= h2 /\
       log (&q2) <= h2 /\
       ~(&b2 * log (&p2 / &q2) - &b1 * log (&p1 / &q1) = &0)
       ==> exp
           (--(&40000 *
               h1 *
               h2 *
               max (&10) (max (log (&b1 / h2 + &b2 / h1)) (log (h1 * h2))) pow
               2)) <=
           abs (&b2 * log (&p2 / &q2) - &b1 * log (&p1 / &q1))
```

### TWOLOG_LOG2_LOG3  (Baker/twolog.ml)
The case log 2, log 3.

```
|- forall b1 b2.
       1 <= b1 /\ 1 <= b2
       ==> exp (--(&45000 * max (&10) (log (&b1 + &b2)) pow 2)) <=
           abs (&b2 * log (&2) - &b1 * log (&3))
```

### STEINER_BOUNDED  (Baker/steiner.ml)
Unconditional (verified enclosures of log 2, log 3 and convergents of log2 3).

```
|- forall n k l. circuit k l n /\ k < 6586818670 ==> n = 1 /\ k = 1 /\ l = 1
```

### STEINER_CIRCUITS  (Baker/steiner.ml)
Steiner (1977): the only circuit of the 3x+1 map is 1 -> 2 -> 1.

```
|- forall n k l. circuit k l n <=> n = 1 /\ k = 1 /\ l = 1
```

## Part IV. Number fields, Thue, Mordell, superelliptic equations, Catalan

### NF_ORDER_NORTHCOTT  (Baker/ant_bridge_nf.ml)
Northcott finiteness for the order Z[r 1]: only finitely many conjugate vectors of the order have all conjugates bounded (from RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE of ANT/complex_embeddings.ml through the bridge of Part XI; the Northcott theorem for algebraic integers of bounded degree and house is COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE there).

```
|- forall n c r R.
       nf_data n c r
       ==> (exists A.
                FINITE A /\
                (forall b. b IN A ==> nf_order n r b) /\
                (forall a.
                     nf_order n r a /\
                     (forall k. k IN 1..n ==> norm (a k) <= R)
                     ==> (exists b.
                              b IN A /\ (forall k. k IN 1..n ==> a k = b k))))
```

### NF_BOX_PRINCIPLE  (Baker/nf_box.ml)
A box principle for the order Z[r 1]: the Minkowski theorem for the ideal C O_K of K = Q(r 1) (NUMBER_FIELD_IDEAL_MINKOWSKI of ANT/minkowski_theory.ml), C the conductor of Z[r 1] in O_K (NF_DATA_CONDUCTOR: an integer C >= 1 with C O_K inside Z[r 1]).

```
|- forall n c r.
       nf_data n c r
       ==> (exists CK.
                &1 <= CK /\
                (forall cj cc.
                     (forall k.
                          k IN 1..n
                          ==> cj k IN 1..n /\
                              r (cj k) = cnj (r k) /\
                              &0 < cc k /\
                              cc (cj k) = cc k) /\
                     CK <= product (1..n) cc
                     ==> (exists a.
                              nf_order n r a /\
                              (forall k.
                                   k IN 1..n
                                   ==> ~(a k = Cx (&0)) /\ norm (a k) <= cc k))))
```

### NF_UNITS_BOUNDED_GENERATION  (Baker/nf_units.ml)
Bounded generation of the units of Z[r 1] (by the box principle and Northcott, without the Dirichlet unit theorem, which ANT/unit_theorem.ml has).

```
|- forall n c r.
       nf_data n c r
       ==> (exists S C1.
                FINITE S /\
                (forall s. s IN S ==> nf_unit n r s) /\
                (forall u X.
                     nf_unit n r u /\
                     (forall k. k IN 1..n ==> abs (log (norm (u k))) <= X)
                     ==> (exists mm.
                              (forall k.
                                   k IN 1..n
                                   ==> u k = cproduct S (\s. s k pow mm s)) /\
                              &(nsum S mm) <= C1 * (&1 + X))))
```

### THUE  (Baker/thue.ml)
Thue's theorem (via Baker): an irreducible binary form of degree >= 3 takes each value finitely often.

```
|- forall n a m.
       3 <= n /\
       (forall i. integer (a i)) /\
       ~(a 0 = &0) /\
       integer m /\
       (forall t.
            vsum (0..n) (\i. Cx (a i) * t pow (n - i)) = Cx (&0)
            ==> (forall d b.
                     d < n /\
                     (forall i. integer (b i)) /\
                     vsum (0..d) (\i. Cx (b i) * t pow i) = Cx (&0)
                     ==> (forall i. i <= d ==> b i = &0)))
       ==> FINITE
           {x,y | integer x /\
                  integer y /\
                  sum (0..n) (\i. a i * x pow (n - i) * y pow i) = m}
```

### CUBIC_FORM_REDUCTION  (Baker/cubic_reduction.ml)
Finiteness of classes of binary cubic forms of given discriminant without rational zero.

```
|- forall D.
       ~(D = &0)
       ==> (exists Phi.
                FINITE Phi /\
                (forall a1 b1 c1 d1.
                     a1,b1,c1,d1 IN Phi
                     ==> integer a1 /\ integer b1 /\ integer c1 /\ integer d1) /\
                (forall a b c d.
                     integer a /\
                     integer b /\
                     integer c /\
                     integer d /\
                     b pow 2 * c pow 2 -
                     &4 * a * c pow 3 -
                     &4 * b pow 3 * d -
                     &27 * a pow 2 * d pow 2 +
                     &18 * a * b * c * d =
                     D /\
                     (forall u v.
                          integer u /\
                          integer v /\
                          a * u pow 3 +
                          b * u pow 2 * v +
                          c * u * v pow 2 +
                          d * v pow 3 =
                          &0
                          ==> u = &0 /\ v = &0)
                     ==> (exists a1 b1 c1 d1 p q r s.
                              a1,b1,c1,d1 IN Phi /\
                              integer p /\
                              integer q /\
                              integer r /\
                              integer s /\
                              p * s - q * r = &1 /\
                              (forall u v.
                                   a * u pow 3 +
                                   b * u pow 2 * v +
                                   c * u * v pow 2 +
                                   d * v pow 3 =
                                   a1 * (p * u + q * v) pow 3 +
                                   b1 *
                                   (p * u + q * v) pow 2 *
                                   (r * u + s * v) +
                                   c1 *
                                   (p * u + q * v) *
                                   (r * u + s * v) pow 2 +
                                   d1 * (r * u + s * v) pow 3))))
```

### MORDELL  (Baker/mordell.ml)
Mordell (1922): y^2 = x^3 + k has finitely many integer solutions.

```
|- forall k.
       integer k /\ ~(k = &0)
       ==> FINITE {x,y | integer x /\ integer y /\ y pow 2 = x pow 3 + k}
```

### NF_PRIMITIVE_ELEMENT  (Baker/nf_fields.ml)
The primitive element theorem in the conjugate-vector framework: finitely many algebraic numbers lie, with a common denominator, in the field of one nf_data (from the integral primitive element NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q of ANT/integrality.ml and NF_DATA_FIELD_CARRIER of the bridge).

```
|- forall s.
       FINITE s /\ (forall z. z IN s ==> algebraic_number z)
       ==> (exists n c r D.
                nf_data n c r /\
                integer D /\
                ~(D = &0) /\
                (forall z.
                     z IN s
                     ==> (exists p.
                              (forall i. integer (p i)) /\
                              Cx D * z =
                              vsum (0..n - 1) (\i. Cx (p i) * r 1 pow i))))
```

### NF_POWER_DESCENT  (Baker/descent.ml)
The descent d (x - alpha) = xi^m with d from a finite set, as conjugate vectors of the order Z[alpha]: from the S-unit descent SCHINZEL_TIJDEMAN_SUNIT_DESCENT of Baker/schinzel_sunit.ml (the S-units and valuations of ANT/, no class number; m divides v_P(x - alpha) outside a fixed finite set of primes, NF_DESCENT_VALUATION) and the conductor of Z[alpha] (NF_DATA_CONDUCTOR).

```
|- forall n c r m R.
       nf_data n c r /\ 1 <= m /\ integer R /\ ~(R = &0)
       ==> (exists D.
                FINITE D /\
                (forall d.
                     d IN D
                     ==> nf_order n r d /\
                         (forall k. k IN 1..n ==> ~(d k = Cx (&0)))) /\
                (forall x y w a b.
                     integer x /\
                     integer y /\
                     integer w /\
                     integer a /\
                     integer b /\
                     ~(sum (0..n) (\i. c i * x pow i) = &0) /\
                     sum (0..n) (\i. c i * x pow i) * w = y pow m /\
                     a * sum (0..n) (\i. c i * x pow i) + b * w = R
                     ==> (exists d xi.
                              d IN D /\
                              nf_order n r xi /\
                              (forall k.
                                   k IN 1..n
                                   ==> d k * (Cx x - r k) = xi k pow m))))
```

### NF_UNIT_EQUATION  (Baker/uniteq.ml)
The unit equation a u + b v = e has finitely many solutions (via Baker).

```
|- forall n c r a b e.
       nf_data n c r /\
       nf_order n r a /\
       nf_order n r b /\
       nf_order n r e /\
       ~(a 1 = Cx (&0)) /\
       ~(b 1 = Cx (&0)) /\
       ~(e 1 = Cx (&0))
       ==> (exists U.
                FINITE U /\
                (forall u v.
                     nf_unit n r u /\
                     nf_unit n r v /\
                     (forall k. k IN 1..n ==> a k * u k + b k * v k = e k)
                     ==> u 1 IN U))
```

### SUPERELLIPTIC  (Baker/superell.ml)
Schinzel-Tijdeman / Baker (1969): y^m = f(x), m >= 3, f with two simple roots, has finitely many integer solutions.

```
|- forall N a m z1 z2.
       3 <= m /\
       (forall i. integer (a i)) /\
       ~(a N = &0) /\
       ~(z1 = z2) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z1 pow (i - 1)) = Cx (&0)) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z2 pow (i - 1)) = Cx (&0))
       ==> FINITE
           {x,y | integer x /\
                  integer y /\
                  y pow m = sum (0..N) (\i. a i * x pow i)}
```

### LEBESGUE  (Baker/lebesgue.ml)
Lebesgue (1850): x^m = y^2 + 1 has no solutions with y >= 1 (the Gaussian integers as the Euclidean ring imag_quadratic_integers 1, IMAG_QUADRATIC_INTEGERS_GAUSSIAN, and UFD_COPRIME_MUL_POW).

```
|- forall m x y. 2 <= m /\ 1 <= y ==> ~(x EXP m = y EXP 2 + 1)
```

### KO_CHAO_EXPONENT_BOUND  (Baker/kochao.ml)
The exponent q in X^2 = Y^q + 1 is bounded.

```
|- exists M.
       forall q X Y.
           prime q /\ ODD q /\ 2 <= X /\ 2 <= Y /\ X EXP 2 = Y EXP q + 1
           ==> q <= M
```

### CATALAN_FINITE  (Baker/catalan_finite.ml)
TIJDEMAN (1976): there are only finitely many consecutive perfect powers.

```
|- FINITE
   {x,y,m,n | 1 <= x /\ 1 <= y /\ 2 <= m /\ 2 <= n /\ x EXP m = y EXP n + 1}
```

## Part V. Two logarithms with Laurent's constants

Interpolation determinants with binomial rows, the g-lemma and Laurent's parameter recipe (M. Laurent, Acta Arith. 133 (2008), at mu = 1); Baker/make.ml sections 10 (rationals, loader Baker/make_laurent.ml) and 13 (number fields).

### LAURENT_RATIONAL  (Baker/laurent.ml)
Laurent (2008), Corollary 2 at mu = 1, for rationals: |b2 log(p2/q2) - b1 log(p1/q1)| >= exp(-32 max(10, log(b1/A2 + b2/A1) + 0.38)^2 A1 A2) (Laurent: 25.2 with mu < 1; TWOLOG_RATIONAL has 40000 and an extra log(h1 h2)).

```
|- forall p1 q1 p2 q2 b1 b2 A1 A2.
       1 <= q1 /\
       q1 < p1 /\
       1 <= q2 /\
       q2 < p2 /\
       1 <= b1 /\
       1 <= b2 /\
       &1 <= A1 /\
       log (&p1) <= A1 /\
       &1 <= A2 /\
       log (&p2) <= A2 /\
       ~(&b2 * log (&p2 / &q2) = &b1 * log (&p1 / &q1))
       ==> exp
           (--(&32 *
               max (&10) (log (&b1 / A2 + &b2 / A1) + &38 / &100) pow 2 *
               A1 *
               A2)) <=
           abs (&b2 * log (&p2 / &q2) - &b1 * log (&p1 / &q1))
```

### LAURENT_RATIONAL_GENERAL  (Baker/laurent.ml)
The same bound for all positive rationals and non-zero integer coefficients of any sign, with A_i >= max(1, log max(p_i, q_i)).

```
|- forall p1 q1 p2 q2 b1 b2 A1 A2.
       1 <= p1 /\
       1 <= q1 /\
       1 <= p2 /\
       1 <= q2 /\
       integer b1 /\
       integer b2 /\
       ~(b1 = &0) /\
       ~(b2 = &0) /\
       &1 <= A1 /\
       log (&(MAX p1 q1)) <= A1 /\
       &1 <= A2 /\
       log (&(MAX p2 q2)) <= A2 /\
       ~(b2 * log (&p2 / &q2) + b1 * log (&p1 / &q1) = &0)
       ==> exp
           (--(&32 *
               max (&10) (log (abs b1 / A2 + abs b2 / A1) + &38 / &100) pow 2 *
               A1 *
               A2)) <=
           abs (b2 * log (&p2 / &q2) + b1 * log (&p1 / &q1))
```

### LAURENT_RATIONAL_PARAM  (Baker/laurent.ml)
Laurent (2008), Theorem 2 at mu = 1, for rationals and any rho in [4, 8]: log |Lambda| >= -laurent_bound rho h a1 a2, Laurent's closed form C (h + lam)^2 a1 a2 + sqrt(omega theta) (h + lam) + log(C' (h + lam)^2 a1 a2), lam = log rho (definitions in Baker/laurent_defs.ml).

```
|- forall p1 q1 p2 q2 b1 b2 rho h a1 a2.
       1 <= q1 /\
       q1 < p1 /\
       1 <= q2 /\
       q2 < p2 /\
       1 <= b1 /\
       1 <= b2 /\
       &4 <= rho /\
       rho <= &8 /\
       &10 <= h /\
       &1 <= a1 /\
       (rho - &1) * log (&p1 / &q1) + &2 * log (&p1) <= a1 /\
       &1 <= a2 /\
       (rho - &1) * log (&p2 / &q2) + &2 * log (&p2) <= a2 /\
       log rho pow 2 <= a1 * a2 /\
       log (&b1 / a2 + &b2 / a1) + log (log rho) + &5 / &2 <= h /\
       ~(&b2 * log (&p2 / &q2) = &b1 * log (&p1 / &q1))
       ==> --laurent_bound rho h a1 a2 <=
           log (abs (&b2 * log (&p2 / &q2) - &b1 * log (&p1 / &q1)))
```

### LAURENT_NF_REAL  (Baker/laurent_alg.ml)
Corollary 2 in a number field K of degree n (nf_data n c r): real
x_i = be_i / ga_i > 1 with algebraic integers be_i, ga_i of K whose pair
heights nf_proj_height are at most A_i; the constant is 32 n^4
(Laurent: 25.2 D^4). These archimedean pair heights are upper bounds for
absolute logarithmic heights, and depend on the chosen coordinates.

```
|- forall n c r be1 ga1 be2 ga2 x1 x2 b1 b2 A1 A2.
       nf_data n c r /\
       nf_alg_int n r be1 /\
       nf_alg_int n r ga1 /\
       nf_alg_int n r be2 /\
       nf_alg_int n r ga2 /\
       ~(ga1 1 = Cx (&0)) /\
       ~(ga2 1 = Cx (&0)) /\
       be1 1 = Cx x1 * ga1 1 /\
       be2 1 = Cx x2 * ga2 1 /\
       &1 < x1 /\
       &1 < x2 /\
       1 <= b1 /\
       1 <= b2 /\
       nf_proj_height n be1 ga1 <= A1 /\
       log x1 <= &n * A1 /\
       &1 <= &n * A1 /\
       nf_proj_height n be2 ga2 <= A2 /\
       log x2 <= &n * A2 /\
       &1 <= &n * A2 /\
       ~(&b2 * log x2 = &b1 * log x1)
       ==> exp
           (--(&32 *
               &n pow 4 *
               max (max (&10 / &n) (&1))
               (log (&b1 / (&n * A2) + &b2 / (&n * A1)) + &38 / &100) pow
               2 *
               A1 *
               A2)) <=
           abs (&b2 * log x2 - &b1 * log x1)
```

### LAURENT_NF_REAL_PARAM  (Baker/laurent_alg.ml)
Theorem 2 at mu = 1 in a number field of degree n (D = n), with Laurent's condition n log 2 / 2 <= h (without it the statement fails for multiplicatively dependent data of huge degree; LAURENT_ALG_REAL_PARAM_DEG20 drops it for n <= 20).

```
|- forall n c r be1 ga1 be2 ga2 x1 x2 b1 b2 rho h a1 a2.
       nf_data n c r /\
       nf_alg_int n r be1 /\
       nf_alg_int n r ga1 /\
       nf_alg_int n r be2 /\
       nf_alg_int n r ga2 /\
       ~(ga1 1 = Cx (&0)) /\
       ~(ga2 1 = Cx (&0)) /\
       be1 1 = Cx x1 * ga1 1 /\
       be2 1 = Cx x2 * ga2 1 /\
       &1 < x1 /\
       &1 < x2 /\
       1 <= b1 /\
       1 <= b2 /\
       &4 <= rho /\
       rho <= &8 /\
       &10 <= h /\
       &1 <= a1 /\
       (rho - &1) * log x1 + &2 * &n * nf_proj_height n be1 ga1 <= a1 /\
       &1 <= a2 /\
       (rho - &1) * log x2 + &2 * &n * nf_proj_height n be2 ga2 <= a2 /\
       log rho pow 2 <= a1 * a2 /\
       &n * (log (&b1 / a2 + &b2 / a1) + log (log rho) + &5 / &2) <= h /\
       &n * log (&2) / &2 <= h /\
       ~(&b2 * log x2 = &b1 * log x1)
       ==> --laurent_bound rho h a1 a2 <=
           log (abs (&b2 * log x2 - &b1 * log x1))
```
## Part VI. The Schinzel-Tijdeman theorem for reducible f

A. Schinzel and R. Tijdeman (Acta Arith. 31, 1976): in y^m = f(x) the
exponent m is bounded as soon as f has two distinct roots. For two roots
with different minimal polynomials two RATIONAL logarithms suffice (the norm
trick); here the three theorems below are corollaries of SCHINZEL_TIJDEMAN
and SCHINZEL_TIJDEMAN_FINITE (Part XIII): an integer polynomial vanishing at
z1 but not at z2 makes the roots distinct
(SCHINZEL_TIJDEMAN_SEPARATING_DISTINCT), and the bound needs neither simple
roots nor a N <> 0. The descent over Z of the norm-trick proof,
INT_POWER_DESCENT_BOUNDED, and the polynomial tools used by Parts XII and
XIII are in Baker/make.ml section 14; the corollaries are at the end of
Baker/schinzel_general.ml (section 20).

### SCHINZEL_TIJDEMAN_REDUCIBLE  (Baker/schinzel_general.ml)
If the integer polynomial f has two simple roots z1, z2 with different minimal polynomials (some integer polynomial vanishes at z1 but not at z2), then y^m = f(x) with integers x, y and |y| >= 2 forces m <= M.

```
|- forall N a z1 z2.
       (forall i. integer (a i)) /\
       ~(a N = &0) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z1 pow (i - 1)) = Cx (&0)) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z2 pow (i - 1)) = Cx (&0)) /\
       (exists d b.
            (forall i. integer (b i)) /\
            vsum (0..d) (\i. Cx (b i) * z1 pow i) = Cx (&0) /\
            ~(vsum (0..d) (\i. Cx (b i) * z2 pow i) = Cx (&0)))
       ==> (exists M.
                forall x y m.
                    integer x /\
                    integer y /\
                    &2 <= abs y /\
                    y pow m = sum (0..N) (\i. a i * x pow i)
                    ==> m <= M)
```

### SCHINZEL_TIJDEMAN_FINITE_REDUCIBLE  (Baker/schinzel_general.ml)
With SUPERELLIPTIC (m fixed): under the same hypotheses the equation y^m = f(x), |y| >= 2, m >= 3, has only finitely many solutions (x, y, m).

```
|- forall N a z1 z2.
       (forall i. integer (a i)) /\
       ~(a N = &0) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z1 pow (i - 1)) = Cx (&0)) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z2 pow (i - 1)) = Cx (&0)) /\
       (exists d b.
            (forall i. integer (b i)) /\
            vsum (0..d) (\i. Cx (b i) * z1 pow i) = Cx (&0) /\
            ~(vsum (0..d) (\i. Cx (b i) * z2 pow i) = Cx (&0)))
       ==> FINITE
           {x,y,m | integer x /\
                    integer y /\
                    &2 <= abs y /\
                    3 <= m /\
                    y pow m = sum (0..N) (\i. a i * x pow i)}
```

### SCHINZEL_TIJDEMAN_REDUCIBLE_MULT  (Baker/schinzel_general.ml)
The exponent bound for two roots of any multiplicity (with different minimal polynomials). Finiteness for fixed m can fail here: y^3 = x^3 (x + 1)^3 has the solutions y = x (x + 1).

```
|- forall N a z1 z2.
       (forall i. integer (a i)) /\
       ~(a N = &0) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       (exists d b.
            (forall i. integer (b i)) /\
            vsum (0..d) (\i. Cx (b i) * z1 pow i) = Cx (&0) /\
            ~(vsum (0..d) (\i. Cx (b i) * z2 pow i) = Cx (&0)))
       ==> (exists M.
                forall x y m.
                    integer x /\
                    integer y /\
                    &2 <= abs y /\
                    y pow m = sum (0..N) (\i. a i * x pow i)
                    ==> m <= M)
```

### INT_POWER_DESCENT_BOUNDED  (Baker/schinzel_descent.ml)
The descent over Z: if G W = c y^m and a G + b W = R, then G is an m-th power up to a rational factor N1 / N2 with N1 | c R and N2 | R.

```
|- forall G W y c R m.
       integer G /\
       integer W /\
       integer y /\
       integer c /\
       integer R /\
       ~(G = &0) /\
       ~(c = &0) /\
       ~(R = &0) /\
       G * W = c * y pow m /\
       (exists a b. integer a /\ integer b /\ a * G + b * W = R)
       ==> (exists N1 N2 Y.
                integer N1 /\
                integer N2 /\
                integer Y /\
                &1 <= N1 /\
                &1 <= N2 /\
                (exists t. integer t /\ c * R = N1 * t) /\
                (exists t. integer t /\ R = N2 * t) /\
                abs G * N2 = N1 * abs Y pow m)
```

## Part VII. The class number one problem

Gauss conjectured (Disquisitiones Arithmeticae, art. 303) that Q(sqrt(-d))
has class number one only for d = 1, 2, 3, 7, 11, 19, 43, 67, 163.
Heegner (1952) gave a proof by modular functions that was accepted only
later; Baker (1966) and Stark (1967) gave the first generally accepted
proofs. Here the route of Baker (Transcendental Number Theory, Ch. 5;
Baker-Wustholz, Logarithmic Forms and Diophantine Geometry, sec. 3.1), after
an idea of Gelfond and Linnik: for d prime, d = 3 mod 4, with h(-d) = 1 the
representation numbers of the principal form write L(s, chi_k) L(s, chi_kd)
as a lattice sum; at s = 1 the limit formula with an exponentially small
error and the class number formulas of Dirichlet for k = 21 and k = 33 give
a linear form in log eps_21 and log eps_33 that is too small: Laurent's
bound (Part V) gives d < 10^16, BAKER_FELDMAN alone gives finiteness, and
two continued-fraction stages (Baker-Davenport reduction) give d <= 46500,
where explicit second reduced forms exclude all d but the nine (a table of
330 witnesses found by a computer search and checked in the proof).
Baker/make.ml section 15; it needs Library/jacobi.ml, 100/dirichlet.ml and
Multivariate/gamma.ml (Jacobi symbols, Dirichlet L-functions, the sine
product); the definitions (Baker/classno_defs.ml) are at the end of
section 5.

Remark. h(D) here is the class number of Gauss, defined as the number of
reduced primitive binary quadratic forms of discriminant D (form_classno);
the dictionary between forms and ideals is formalised for class number
one in Part VIII (the ring of integers of Q(sqrt(-d)) is a
UFD, equivalently a PID, iff form_classno (qdisc d) = 1), the general
bijection between form classes and ideal classes is not; nor is genus
theory (it is replaced by explicit witness forms,
CLASSNO_ONE_CASES and CLASSNO_WITNESS). The characters are Jacobi symbols
n -> (n | m) (qchar); the class number formulas are used in absolute value
only, with the character sums T in place of the class numbers h(-21 d),
h(-33 d).

### CLASS_NUMBER_ONE  (Baker/classno_main.ml)
Theorem 5.1 of Baker (Transcendental Number Theory, Ch. 5): for squarefree d the discriminant of Q(sqrt(-d)) has exactly one reduced primitive form, i.e. class number one in the sense of Gauss, iff d is one of the nine values of Gauss.

```
|- forall d.
       squarefree d
       ==> (form_classno (qdisc d) = 1 <=>
            d IN {1, 2, 3, 7, 11, 19, 43, 67, 163})
```

### CLASS_NUMBER_ONE_BOUND_LAURENT  (Baker/classno_main.ml)
The effective bound d < 10^16, from the linear form below and the Laurent bound LAURENT_NF_REAL in Q(sqrt 21, sqrt 33) (CLASSNO_LAURENT_INSTANCE), without continued fractions.

```
|- forall d. squarefree d /\ form_classno (qdisc d) = 1 ==> d < 10 EXP 16
```

### CLASS_NUMBER_ONE_FINITE  (Baker/classno_main.ml)
Finiteness (also by the qualitative route alone: CLASS_NUMBER_ONE_FINITE_BAKER applies BAKER_FELDMAN to the linear form, as Baker in 1966).

```
|- FINITE {d | squarefree d /\ form_classno (qdisc d) = 1}
```

### CLASSNO_REPRESENTATION  (Baker/classno_rep.ml)
For d prime, d = 3 mod 4, d > 3, of class number one, the principal form x^2 + x y + ((d + 1)/4) y^2 represents l >= 1 exactly 2 sum_{m | l} (m | d) times: the only use of h(-d) = 1 in the analytic argument (arithmetic of Z[(1 + sqrt(-d))/2] on integer pairs, Jacobi reciprocity).

```
|- forall d l.
       prime d /\ d MOD 4 = 3 /\ 3 < d /\ form_classno (-- &d) = 1 /\ 1 <= l
       ==> &(prin_rep d l) = &2 * sum {m | m divides l} (\m. qchar d m)
```

### CLASSNO_PRODUCT_LIMIT  (Baker/classno_product.ml)
For k = 21, 33 and d as above (d > k): L(1, chi_k) L(1, chi_kd) = zeta_k(2) + sum_{y >= 1} S_y(1), the lattice sum over the principal form at s = 1, as the limit s -> 1+ of the Dirichlet product identity for s > 1.

```
|- forall k d.
       (k = 21 \/ k = 33) /\
       prime d /\
       d MOD 4 = 3 /\
       k < d /\
       form_classno (-- &d) = 1
       ==> (exists S.
                (qform_slice k (&1) (&1) (&((d + 1) DIV 4)) (&1) real_sums S)
                (from 1) /\
                Lfunction (\n. Cx (qchar k n)) *
                Lfunction (\n. Cx (qchar (k * d) n)) =
                Cx (zeta_coprime k + S))
```

### CLASSNO_SLICE_BOUND  (Baker/classno_product.ml)
The limit formula: the slices S_y(1) sum to at most (4 pi / sqrt d) eta (1 + eta) / (1 - eta)^3, eta = exp(-pi sqrt(d) / k), with no class number hypothesis (QFORM_SLICE_BOUND of the general form layer for k = 3 * 7, 3 * 11: the Poisson kernel identity from the sine product, Ramanujan sums).

```
|- forall k d S.
       (k = 21 \/ k = 33) /\
       d MOD 4 = 3 /\
       coprime (k,d) /\
       (qform_slice k (&1) (&1) (&((d + 1) DIV 4)) (&1) real_sums S) (from 1)
       ==> abs S <=
           &4 *
           pi / sqrt (&d) *
           exp (--(pi * sqrt (&d) / &k)) *
           (&1 + exp (--(pi * sqrt (&d) / &k))) /
           (&1 - exp (--(pi * sqrt (&d) / &k))) pow 3
```

### CLASSNO_L1_ODD  (Baker/classno_gauss.ml)
The class number formula of Dirichlet in absolute value for squarefree q = 3 mod 4: |L(1, chi_q)| = pi T / ((2 - chi_q(2)) sqrt q), T = |sum_{a <= (q - 1)/2} chi_q(a)| (Gauss sums without their sign; the even case CLASSNO_L1_EVEN gives |L(1, chi_21)| = 2 log eps_21 / sqrt 21 and |L(1, chi_33)| = 2 log eps_33 / sqrt 33, CLASSNO_L1_REAL).

```
|- forall q.
       squarefree q /\ q MOD 4 = 3
       ==> norm (Lfunction (\n. Cx (qchar q n))) =
           pi *
           abs (sum (1..(q - 1) DIV 2) (\a. qchar q a)) /
           ((&2 - qchar q 2) * sqrt (&q))
```

### CLASSNO_LINEAR_FORM  (Baker/classno_linear.ml)
The linear form in two logarithms of Baker, Ch. 5, sec. 4: for d prime, d = 3 mod 8, d > 10^4, of class number one, 0 < |b2 log eps_33 - b1 log eps_21| <= 8800 exp(-pi sqrt(d) / 33) with 1 <= b1 <= 391 sqrt d, 1 <= b2 <= 160 sqrt d (b1 = 105 T21, b2 = 22 T33).

```
|- forall d.
       prime d /\ d MOD 8 = 3 /\ 10000 < d /\ form_classno (-- &d) = 1
       ==> (exists b1 b2.
                1 <= b1 /\
                1 <= b2 /\
                &b1 <= &391 * sqrt (&d) /\
                &b2 <= &160 * sqrt (&d) /\
                ~(&b2 * log (&23 + &4 * sqrt (&33)) =
                  &b1 * log ((&5 + sqrt (&21)) / &2)) /\
                abs
                (&b2 * log (&23 + &4 * sqrt (&33)) -
                 &b1 * log ((&5 + sqrt (&21)) / &2)) <=
                &8800 * exp (--(pi * sqrt (&d) / &33)))
```

### The definitions  (Baker/classno_defs.ml)
Reduced forms, the class number of Gauss and the field discriminant (as printed by HOL; `{a,b,c | ...}` is a set of triples of integers).

```
|- forall a c b.
       qf_reduced a b c <=>
       &0 < a /\ abs b <= a /\ a <= c /\ (abs b = a \/ a = c ==> &0 <= b)
|- forall D.
       form_classno D =
       CARD
       {a,b,c | qf_reduced a b c /\
                b pow 2 - &4 * a * c = D /\
                gcd (a,gcd (b,c)) = &1}
|- forall d. qdisc d = (if d MOD 4 = 3 then -- &d else --(&4 * &d))
```

## Part VIII. Unique factorization in imaginary quadratic fields

The ring-theoretic form of the class number one theorem, built on the
algebraic number theory of ANT/ (Part XI). For every d the ring of algebraic
integers of Q(sqrt(-d)) inside C (imag_quadratic_integers d, the ring of
integers of the number field imag_quadratic_field d in the sense of ANT:
RING_OF_INTEGERS_IMAG_QUADRATIC_FIELD) is a unique factorization domain,
equivalently a principal ideal domain, equivalently of class number one,
exactly when d = m^2 k with k one of the nine of Gauss (the field depends
only on the squarefree part of d; m = 0 is the degenerate field Q with the
ring Z). Intrinsically: a number field of degree 2 with negative
discriminant has class number one iff its discriminant is -3, -4, -7, -8,
-11, -19, -43, -67 or -163 (every such field is isomorphic to a complex
Q(sqrt(-d)) with d_k = qdisc d, and isomorphic number fields have equal
class numbers). UFD and PID are the notions of Library/ringtheory.ml
(UFD_EQ_UNIQUE_FACTORIZATION spells out unique factorization into
irreducibles); UFD, PID and ideal class number one are equivalent for
Dedekind domains (ANT). The dictionary for class number one, squarefree d:
the algebraic integers of the field are Z[omega], omega = (1 + sqrt(-d))/2
or sqrt(-d) (QUADRATIC_FIELD_INTEGRAL_BASIS of ANT), and qdisc d = d_K; a
UFD has class number one in the sense of forms (a second reduced form (a, b,
c) gives a prime p | a that is irreducible but not prime); form class number
one gives a PID (every ideal is c (Z a + Z (b + omega)), whose norm form has
discriminant qdisc d, is equivalent to the principal form and so represents
1, which gives a generator). Baker/make.ml section 16; the field
Q(sqrt(-d)), its discriminant and its ring of integers are the imaginary
quadratic base files at the end of section 5 (Baker/quadint_defs.ml,
Baker/quadint_ant.ml, Baker/quadint_ring.ml, after the definitions
Baker/classno_defs.ml).

### IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE  (Baker/quadint_intrinsic.ml)
The Baker-Heegner-Stark theorem for abstract number fields: a number field of degree 2 with negative discriminant has class number one iff its discriminant is one of the nine (IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE_UFD and _PID: the same for UFD and PID).

```
|- forall k.
       number_field k /\
       extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
       number_field_discriminant k < &0
       ==> (class_number (ring_of_integers k) = 1 <=>
            number_field_discriminant k IN
            {-- &3, -- &4, -- &7, -- &8, -- &11, -- &19, -- &43, -- &67,
             -- &163})
```

### CLASS_NUMBER_ONE_UFD  (Baker/quadint_main.ml)
For every d the ring of integers of Q(sqrt(-d)) is a UFD iff d = m^2 k with k one of the nine values of Gauss (with CLASS_NUMBER_ONE of Part VII; m = 0 is the degenerate field Q).

```
|- forall d.
       UFD (imag_quadratic_integers d) <=>
       (exists m k.
            d = m EXP 2 * k /\ k IN {1, 2, 3, 7, 11, 19, 43, 67, 163})
```

### CLASS_NUMBER_ONE_PID  (Baker/quadint_main.ml)
The same for principal ideal domains.

```
|- forall d.
       PID (imag_quadratic_integers d) <=>
       (exists m k.
            d = m EXP 2 * k /\ k IN {1, 2, 3, 7, 11, 19, 43, 67, 163})
```

### CLASS_NUMBER_ONE_IDEAL_CLASSES  (Baker/quadint_main.ml)
The same for ideal class number one.

```
|- forall d.
       class_number (imag_quadratic_integers d) = 1 <=>
       (exists m k.
            d = m EXP 2 * k /\ k IN {1, 2, 3, 7, 11, 19, 43, 67, 163})
```

### CLASS_NUMBER_ONE_UNIQUE_FACTORIZATION  (Baker/quadint_main.ml)
The explicit statement: every nonzero element is associate to a product of irreducibles, unique up to order and associates, iff d = m^2 k with k one of the nine.

```
|- forall d.
       (forall x.
            x IN ring_carrier (imag_quadratic_integers d) /\ ~(x = Cx (&0))
            ==> (exists n p.
                     (forall i.
                          1 <= i /\ i <= n
                          ==> ring_irreducible (imag_quadratic_integers d)
                              (p i)) /\
                     ring_associates (imag_quadratic_integers d)
                     (ring_product (imag_quadratic_integers d) (1..n) p)
                     x /\
                     (forall m q.
                          (forall j.
                               1 <= j /\ j <= m
                               ==> ring_irreducible
                                   (imag_quadratic_integers d)
                                   (q j)) /\
                          ring_associates (imag_quadratic_integers d)
                          (ring_product (imag_quadratic_integers d) (1..m) q)
                          x
                          ==> (exists f.
                                   IMAGE f (1..n) = 1..m /\
                                   (forall i j.
                                        1 <= i /\ i <= n /\ 1 <= j /\ j <= n
                                        ==> (f i = f j <=> i = j)) /\
                                   (forall i.
                                        1 <= i /\ i <= n
                                        ==> ring_associates
                                            (imag_quadratic_integers d)
                                            (p i)
                                            (q (f i))))))) <=>
       (exists m k.
            d = m EXP 2 * k /\ k IN {1, 2, 3, 7, 11, 19, 43, 67, 163})
```

### QUAD_UFD_EQ_CLASSNO_ONE  (Baker/quadint_main.ml)
The dictionary for class number one: unique factorization iff form_classno (qdisc d) = 1 (QUAD_PID_EQ_CLASSNO_ONE: the same for PID; IMAG_QUADRATIC_CLASS_NUMBER_1_EQ_FORMS: for the ideal class number).

```
|- forall d.
       squarefree d
       ==> (UFD (imag_quadratic_integers d) <=> form_classno (qdisc d) = 1)
```

### IMAGINARY_QUADRATIC_FIELD_ISOMORPHIC  (Baker/quadint_intrinsic.ml)
Every number field of degree 2 with negative discriminant is isomorphic to a complex Q(sqrt(-d)), d squarefree with discriminant qdisc d (from QUADRATIC_FIELD_SQRT and QUADRATIC_FIELD_UNIQUE of ANT).

```
|- forall k.
       number_field k /\
       extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
       number_field_discriminant k < &0
       ==> (exists d.
                squarefree d /\
                number_field_discriminant k = qdisc d /\
                k isomorphic_ring
                subring_generated complex_ring (imag_quadratic_field d))
```

### IMAG_QUADRATIC_FIELD_DISCRIMINANT  (Baker/quadint_ant.ml)
qdisc d is the discriminant of the number field Q(sqrt(-d)) (squarefree d; QUADRATIC_FIELD_DISCRIMINANT of ANT).

```
|- forall d.
       squarefree d
       ==> number_field_discriminant
           (subring_generated complex_ring (imag_quadratic_field d)) =
           qdisc d
```

### RING_OF_INTEGERS_IMAG_QUADRATIC_FIELD  (Baker/quadint_ant.ml)
The ring of integers of Q(sqrt(-d)) in the sense of ANT is imag_quadratic_integers d, as rings (all d); hence a Dedekind domain (DEDEKIND_IMAG_QUADRATIC_INTEGERS).

```
|- forall d.
       ring_of_integers
       (subring_generated complex_ring (imag_quadratic_field d)) =
       imag_quadratic_integers d
```

### IMAG_QUADRATIC_INTEGERS_SQUARE_MUL  (Baker/quadint_ant.ml)
The ring depends only on the squarefree part of d (likewise the field: IMAG_QUADRATIC_FIELD_SQUARE_MUL).

```
|- forall m k.
       ~(m = 0)
       ==> imag_quadratic_integers (m EXP 2 * k) = imag_quadratic_integers k
```

### IMAG_QUADRATIC_INTEGERS_CARRIER  (Baker/quadint_ring.ml)
For squarefree d the algebraic integers of the field are Z[omega] (from the integral basis of ANT/quadratic.ml).

```
|- forall d.
       squarefree d
       ==> ring_carrier (imag_quadratic_integers d) =
           {z | exists x y.
                    integer x /\ integer y /\ z = Cx x + Cx y * quad_omega d}
```

### The definitions  (Baker/quadint_defs.ml)
The generator omega, the field and its ring of integers (subring_generated of Library/ringtheory.ml, complex_ring of Multivariate/complex_ring.ml, algebraic_integer of Baker/algint.ml).

```
|- forall d.
       quad_omega d =
       (if d MOD 4 = 3
        then (Cx (&1) + ii * Cx (sqrt (&d))) / Cx (&2)
        else ii * Cx (sqrt (&d)))
|- forall d.
       imag_quadratic_field d =
       {z | exists a b.
                rational a /\
                rational b /\
                z = Cx a + Cx b * ii * Cx (sqrt (&d))}
|- forall d.
       imag_quadratic_integers d =
       subring_generated complex_ring
       {z | algebraic_integer z /\ z IN imag_quadratic_field d}
```

## Part IX. Unique factorization at work: Ramanujan-Nagell, Fermat, FLT 3

Classical Diophantine equations solved by unique factorization in the rings
of integers of Q(sqrt(-7)), Q(sqrt(-2)) and Q(sqrt(-3)). These rings are
UFDs by the Euclidean algorithm, without CLASS_NUMBER_ONE_UFD (Part VIII)
and the class number one theorem: for d = 1, 2, 3, 7, 11 every complex
number lies at distance less than 1 from the ring
(IMAG_QUADRATIC_INTEGERS_NEAR), so the ring is Euclidean for the norm
(IMAG_QUADRATIC_INTEGERS_EUCLIDEAN), hence a PID and a UFD
(IMAG_QUADRATIC_INTEGERS_PID, IMAG_QUADRATIC_INTEGERS_UFD of
Baker/quadint_ring.ml, an imaginary quadratic base file at the end of
section 5). The common tool is a library-style lemma for any unique
factorization domain: coprime factors of a k-th power are units times k-th
powers (UFD_COPRIME_MUL_POW). Baker/make.ml section 17 (it needs only
ANT/ufd.ml and the imaginary quadratic base files of section 5).

### RAMANUJAN_NAGELL  (Baker/ramanujan_nagell.ml)
Ramanujan (1913), Nagell (1948): the only natural solutions of x^2 + 7 = 2^n (Nagell: unique factorization in Z[(1 + sqrt(-7))/2] and a 7-adic argument for the sequence b(m+2) = b(m+1) - 2 b(m)).

```
|- forall x n.
       x EXP 2 + 7 = 2 EXP n <=>
       x = 1 /\ n = 3 \/
       x = 3 /\ n = 4 \/
       x = 5 /\ n = 5 \/
       x = 11 /\ n = 7 \/
       x = 181 /\ n = 15
```

### FERMAT_SQUARE_CUBE  (Baker/fermat26.ml)
Fermat, Euler: for integers x and y, x^2 + 2 = y^3 only for x = +-5,
y = 3. The proof uses unique factorization in Z[sqrt(-2)].

```
|- forall x y:int.
       x pow 2 + &2 = y pow 3 <=> (x = &5 \/ x = -- &5) /\ y = &3
```

### FERMAT_26  (Baker/fermat26.ml)
Hence 26 is the only natural number between a square and a cube.

```
|- forall n.
       (exists x. n = x EXP 2 + 1) /\ (exists y. n + 1 = y EXP 3) <=> n = 26
```

### FLT3  (Baker/flt3.ml)
Fermat Last Theorem for the exponent 3 (Euler; the classical descent in the Eisenstein integers Z[(1 + sqrt(-3))/2]); FLT3_INT is the version over the integers.

```
|- forall x y z. x EXP 3 + y EXP 3 = z EXP 3 ==> x = 0 \/ y = 0
```

### FLT3_INT  (Baker/flt3.ml)
The integer version.

```
|- forall x y z:int.
       x pow 3 + y pow 3 = z pow 3 ==> x * y * z = &0
```

### IMAG_QUADRATIC_INTEGERS_UFD  (Baker/quadint_ring.ml)
The Euclidean imaginary quadratic rings: for d = 1, 2, 3, 7, 11 the ring of integers of Q(sqrt(-d)) is Euclidean for the norm, hence a PID (IMAG_QUADRATIC_INTEGERS_EUCLIDEAN, IMAG_QUADRATIC_INTEGERS_PID) and a UFD; d = 1 gives the Gaussian integers of LEBESGUE (IMAG_QUADRATIC_INTEGERS_GAUSSIAN).

```
|- forall d. d IN {1, 2, 3, 7, 11} ==> UFD (imag_quadratic_integers d)
```

### UFD_COPRIME_MUL_POW  (ANT/ufd.ml)
The library-style lemma, for any unique factorization domain.

```
|- forall r a b c k.
       UFD r /\
       a IN ring_carrier r /\
       b IN ring_carrier r /\
       c IN ring_carrier r /\
       ring_coprime r (a,b) /\
       ring_mul r a b = ring_pow r c k
       ==> (exists u e.
                ring_unit r u /\
                e IN ring_carrier r /\
                a = ring_mul r u (ring_pow r e k))
```

## Part X. The hyperelliptic equation and integral points on elliptic curves

Baker (1968-69): the equation y^2 = f(x) has only finitely many integer
solutions when f has at least three simple roots (Siegel 1926 non-
effectively), and so has every elliptic curve in Weierstrass form (Siegel
1929 for integral points of genus one); together with SUPERELLIPTIC (Part
IV) this covers y^m = f(x) for all m >= 2. The route: the descent of
SUPERELLIPTIC at three roots, the Siegel identity among the three roots, one
unit equation (NF_UNIT_EQUATION) and an explicit recovery of x. MORDELL
(Part IV) is the case a = 0 of ELLIPTIC_INTEGRAL_POINTS. Baker/make.ml
section 18 (it needs ANT/ and sections 1 to 6, 11 and 12).

### HYPERELLIPTIC  (Baker/hyperell.ml)
Baker (1969), qualitative form: three distinct simple roots give finitely many integral points on y^2 = f(x).

```
|- forall N a z1 z2 z3.
       (forall i. integer (a i)) /\
       ~(a N = &0) /\
       ~(z1 = z2) /\
       ~(z1 = z3) /\
       ~(z2 = z3) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z1 pow (i - 1)) = Cx (&0)) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z2 pow (i - 1)) = Cx (&0)) /\
       vsum (0..N) (\i. Cx (a i) * z3 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z3 pow (i - 1)) = Cx (&0))
       ==> FINITE
           {x,y | integer x /\
                  integer y /\
                  y pow 2 = sum (0..N) (\i. a i * x pow i)}
```

### SUPERELLIPTIC_SIMPLE_ROOTS  (Baker/hyperell.ml)
All exponents m >= 2 at once: at least three simple roots for m = 2, two for m >= 3.

```
|- forall N a m.
       2 <= m /\
       (forall i. integer (a i)) /\
       ~(a N = &0) /\
       (if m = 2 then 3 else 2) <=
       CARD
       {z | vsum (0..N) (\i. Cx (a i) * z pow i) = Cx (&0) /\
            ~(vsum (1..N) (\i. Cx (&i * a i) * z pow (i - 1)) = Cx (&0))}
       ==> FINITE
           {x,y | integer x /\
                  integer y /\
                  y pow m = sum (0..N) (\i. a i * x pow i)}
```

### ELLIPTIC_INTEGRAL_POINTS  (Baker/elliptic.ml)
Baker (1968): an elliptic curve y^2 = x^3 + a x + b (4 a^3 + 27 b^2 <> 0) has only finitely many integral points.

```
|- forall a b.
       integer a /\ integer b /\ ~(&4 * a pow 3 + &27 * b pow 2 = &0)
       ==> FINITE
           {x,y | integer x /\ integer y /\ y pow 2 = x pow 3 + a * x + b}
```

### ELLIPTIC_CUBIC_INTEGRAL_POINTS  (Baker/elliptic.ml)
The same for y^2 = a x^3 + b x^2 + c x + d with non-zero discriminant.

```
|- forall a b c d.
       integer a /\
       integer b /\
       integer c /\
       integer d /\
       ~(a = &0) /\
       ~(b pow 2 * c pow 2 -
         &4 * a * c pow 3 -
         &4 * b pow 3 * d -
         &27 * a pow 2 * d pow 2 +
         &18 * a * b * c * d =
         &0)
       ==> FINITE
           {x,y | integer x /\
                  integer y /\
                  y pow 2 = a * x pow 3 + b * x pow 2 + c * x + d}
```

### WEIERSTRASS_INTEGRAL_POINTS  (Baker/elliptic.ml)
The general Weierstrass form, with the discriminant Delta written out.

```
|- forall a1 a2 a3 a4 a6.
       integer a1 /\
       integer a2 /\
       integer a3 /\
       integer a4 /\
       integer a6 /\
       ~(let b2 = a1 pow 2 + &4 * a2
         and b4 = &2 * a4 + a1 * a3
         and b6 = a3 pow 2 + &4 * a6
         and b8 =
             a1 pow 2 * a6 +
             &4 * a2 * a6 - a1 * a3 * a4 +
             a2 * a3 pow 2 - a4 pow 2 in
         &9 * b2 * b4 * b6 - b2 pow 2 * b8 - &8 * b4 pow 3 - &27 * b6 pow 2 =
         &0)
       ==> FINITE
           {x,y | integer x /\
                  integer y /\
                  y pow 2 + a1 * x * y + a3 * y =
                  x pow 3 + a2 * x pow 2 + a4 * x + a6}
```

## Part XI. Algebraic number theory: the library ANT/ and the bridges

ANT/ is the algebraic number theory library of the HOL Light tree
(91 files and the loader ANT/make.ml), independent of Baker/: Dedekind
domains and their valuations, number fields and rings of integers, ideal
class groups, the splitting of primes, discriminants and differents, the
Hilbert theory of Galois extensions, units and S-units, Minkowski theory,
quadratic and cyclotomic fields, absolute values and places, the Dedekind
zeta function and the Frobenius density theorem. ANT/README describes its
contents, conventions and main theorems, and the header of every ANT file
lists the main results of the file; they are not repeated here. The files of
Baker/ load the ANT files they use through their needs lines (57 of the 91).

The conventions (ANT/README): number fields are abstract, number_field k for
a ring k : A ring, a field of characteristic 0 that is a finite extension of
its prime subfield Q = subfield_generated k {ring_0 k}; the embeddings into
C are a separate notion, complex_embeddings k; the ring of integers
ring_of_integers k is the subring of the elements integral over Z
(integer_ring along ring_of_int k). Extensions are ring homomorphisms
(k,l) h; the relative notions take these arguments and the absolute ones are
their instances over the prime subfield, (subfield_generated k {ring_0 k},k)
I. Theorems carry the plain names in the general form; an absolute form is a
separate theorem only when it is not a one-step instance of the general one,
with the suffix _Q (or _IN_C for subfields of C). Dedekind domains are
treated in general (dedekind_domain r), with the valuations
dedekind_valuation (r,k) h P on a field of fractions k of r; ideal_norm r j
is the cardinality of r/j. The trace, norm and discriminant of a basis are
those of Library/ring_det.ml, Galois theory that of Library/galois.ml,
complex_ring that of Multivariate/complex_ring.ml. The ANT files contain no
priority settings.

The ANT results that Baker/ cites, by topic (the ANT file in parentheses,
then the use in Baker/):

- Number fields and algebraic integers: number_field, ring_of_integers,
  RING_OF_INTEGERS_CARRIER, NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC
  (finitely many algebraic elements generate a number field),
  ROOT_OF_UNITY_IN_RING_OF_INTEGERS (ANT/numfield.ml); integral_element,
  INTEGRAL_CLOSURE_SUBRING, INTEGRAL_ELEMENT_PRIME_SUBFIELD
  (ANT/integral.ml); COMPLEX_PRIME_SUBFIELD (the prime subfield of C is
  {Cx q | rational q}, ANT/complex_embeddings.ml): the algebraic integers
  and the subfields of C of section 5.
- Complex embeddings and conjugates: complex_embeddings,
  COMPLEX_EMBEDDINGS_HAS_SIZE (k has [k:Q] embeddings),
  COMPLEX_EMBEDDINGS_MONOMORPHISM, RING_OF_INTEGERS_CONJUGATES_POLYFUN (the
  conjugates of an algebraic integer are the roots of a monic integer
  polynomial), RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE (Northcott),
  COMPLEX_POLYFUN_MONIC_COEFF_BOUND (ANT/complex_embeddings.ml);
  NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS,
  NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS, COMPLEX_EMBEDDINGS_NORM_EQ
  (ANT/infinite_places.ml); NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q
  (ANT/integrality.ml): the conjugate-vector number fields (sections 11 and
  12) and the number field tools of Sharpening I (section 6).
- Minkowski theory and the index: NUMBER_FIELD_IDEAL_MINKOWSKI
  (ANT/minkowski_theory.ml), NUMBER_FIELD_POLY_DISCRIMINANT_INDEX
  (ANT/power_basis_index.ml): the box principle NF_BOX_PRINCIPLE (Part IV).
- Valuations and S-units: dedekind_valuation (ANT/dedekind_valuation.ml);
  NUMBER_FIELD_VALUATION_MUL, NUMBER_FIELD_VALUATION_POW,
  NUMBER_FIELD_VALUATION_FINITE, NUMBER_FIELD_ROOT_DENOMINATOR
  (ANT/nf_valuation.ml); s_unit_group,
  NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION, S_UNIT_GROUP_GENERATORS_MOD_POW
  (ANT/sunits.ml); RING_OF_INTEGERS_IDEAL_NORM_INTEGER
  (ANT/ring_of_integers.ml): the S-unit descent (section 12) and the
  denominators of p-th roots of Sharpening I (section 6).
- Quadratic fields and class numbers: QUADRATIC_FIELD_DISCRIMINANT,
  QUADRATIC_FIELD_INTEGRAL_BASIS, QUADRATIC_FIELD_SQRT_EXISTS,
  QUADRATIC_FIELD_UNIQUE, INT_NORM_FORM_4_IMAGINARY (ANT/quadratic.ml);
  QUADRATIC_FIELD_UNITS_IMAGINARY_GENERIC (ANT/quadratic_units.ml);
  DEDEKIND_RING_OF_INTEGERS (ANT/ring_of_integers.ml); DEDEKIND_UFD_IFF_PID
  (ANT/dedekind_struct.ml); class_number, NUMBER_FIELD_CLASS_GROUP_FINITE,
  NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1, NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC
  (ANT/classgroup.ml); number_field_discriminant (ANT/discriminant.ml);
  UFD_COPRIME_MUL_POW (ANT/ufd.ml): LEBESGUE and Parts VIII and IX.
- Cyclotomic fields: CYCLOTOMIC_POLY_SPLITS, CYCLOTOMIC_POLY_EVAL_1
  (ANT/cyclotomic_poly.ml), CYCLOTOMIC_FIELD_GALOIS_EXTENSION,
  CYCLOTOMIC_FIELD_GALOIS_GROUP_ROOT (ANT/cyclotomic_galois.ml): the
  cyclotomic unit of Part XV.
- Analytic tools of the library files: REAL_INFSUM_ZETA_BOUNDS and
  REAL_SUMMABLE_POS_PARTIAL_BOUND (Multivariate/realanalysis.ml): the
  lattice series of Parts VII and XV.

The ANT theorems behind the S-unit descent are listed at the end of Part XIII.

### The bridges (Baker/make.ml sections 5 and 11)

Three files connect ANT/ with the complex objects of Baker/: the algebraic
integers and the subfields of C (Baker/algint.ml and
Baker/ant_bridge_complex.ml, section 5) and the conjugate-vector number
fields (Baker/ant_bridge_nf.ml, section 11): nf_data n c r gives the number
field K = Q(r 1) of degree n with its n embeddings nf_embedding n r k, the
conjugate vectors nf_elem, nf_alg_int, nf_order and nf_unit are those of K,
O_K, Z[r 1] and the units of Z[r 1], the product and the sum of the
conjugates are the norm and the trace, and the Northcott finiteness of
Z[r 1] (NF_ORDER_NORTHCOTT, Part IV) is that of O_K. The imaginary quadratic
fields of Part VIII are built on ANT directly.

### INTEGRAL_ELEMENT_COMPLEX_RING  (Baker/algint.ml)
Integral over Z in complex_ring is algebraic_integer of Baker/algint.ml, which derives the closure of the algebraic integers from it.

```
|- forall z.
       integral_element (integer_ring,complex_ring)
       (ring_of_int complex_ring)
       z <=>
       algebraic_integer z
```

### RING_OF_INTEGERS_COMPLEX_SUBFIELD  (Baker/ant_bridge_complex.ml)
The ring of integers of a subfield of C consists of its algebraic integers.

```
|- forall s.
       s subfield_of complex_ring
       ==> ring_carrier (ring_of_integers (subring_generated complex_ring s)) =
           {z | z IN s /\ algebraic_integer z}
```

### NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED  (Baker/ant_bridge_complex.ml)
Finitely many algebraic numbers generate a number field (from NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC of ANT/numfield.ml).

```
|- forall s.
       FINITE s /\ (forall z. z IN s ==> algebraic_number z)
       ==> number_field (subfield_generated complex_ring s)
```

### NF_DATA_NUMBER_FIELD  (Baker/ant_bridge_nf.ml)
The field of an nf_data is a number field of degree n.

```
|- forall n c r.
       nf_data n c r
       ==> number_field (subfield_generated complex_ring {r 1}) /\
           extension_degree
           (subfield_generated complex_ring {Cx (&0)},
            subfield_generated complex_ring {r 1})
           I =
           n
```

### NF_DATA_FIELD_CARRIER  (Baker/ant_bridge_nf.ml)
The elements of K are the P(r 1)/d with an integer polynomial P of degree < n and an integer d <> 0 (used by NF_PRIMITIVE_ELEMENT).

```
|- forall n c r.
       nf_data n c r
       ==> ring_carrier (subfield_generated complex_ring {r 1}) =
           {x | exists d p.
                    integer d /\
                    ~(d = &0) /\
                    (forall i. integer (p i)) /\
                    Cx d * x = vsum (0..n - 1) (\i. Cx (p i) * r 1 pow i)}
```

### NF_EMBEDDING_ALL  (Baker/ant_bridge_nf.ml)
Every ring homomorphism into C is one of the n embeddings.

```
|- forall n c r f.
       nf_data n c r /\
       ring_homomorphism (subfield_generated complex_ring {r 1},complex_ring)
       f
       ==> (exists k.
                k IN 1..n /\
                (forall x.
                     x IN
                     ring_carrier (subfield_generated complex_ring {r 1})
                     ==> f x = nf_embedding n r k x))
```

### NF_DATA_COMPLEX_EMBEDDINGS  (Baker/ant_bridge_nf.ml)
Restricted to K, the n embeddings nf_embedding n r k are the complex embeddings of ANT, pairwise distinct.

```
|- forall n c r.
       nf_data n c r
       ==> complex_embeddings (subfield_generated complex_ring {r 1}) =
           IMAGE
           (\k.
                RESTRICTION
                (ring_carrier (subfield_generated complex_ring {r 1}))
                (nf_embedding n r k))
           (1..n) /\
           (forall k l.
                k IN 1..n /\
                l IN 1..n /\
                RESTRICTION
                (ring_carrier (subfield_generated complex_ring {r 1}))
                (nf_embedding n r k) =
                RESTRICTION
                (ring_carrier (subfield_generated complex_ring {r 1}))
                (nf_embedding n r l)
                ==> k = l)
```

### NF_ALG_INT_EMBEDDINGS  (Baker/ant_bridge_nf.ml)
nf_alg_int vectors are the conjugate vectors of the ring of integers (likewise nf_elem, nf_order, nf_unit).

```
|- forall n c r a.
       nf_data n c r
       ==> (nf_alg_int n r a <=>
            (exists x.
                 x IN
                 ring_carrier
                 (ring_of_integers (subfield_generated complex_ring {r 1})) /\
                 (forall k. k IN 1..n ==> a k = nf_embedding n r k x)))
```

### NF_NORM_NUMBER_FIELD_NORM  (Baker/ant_bridge_nf.ml)
The norm is the product of the conjugates (NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS of ANT/infinite_places.ml).

```
|- forall n c r x.
       nf_data n c r /\
       x IN ring_carrier (subfield_generated complex_ring {r 1})
       ==> algebra_norm
           (subfield_generated (subfield_generated complex_ring {r 1})
            {ring_0 (subfield_generated complex_ring {r 1})},
            subfield_generated complex_ring {r 1})
           I
           x =
           cproduct (1..n) (\k. nf_embedding n r k x)
```

### NF_TRACE_NUMBER_FIELD_TRACE  (Baker/ant_bridge_nf.ml)
The trace is the sum of the conjugates (NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS of ANT/infinite_places.ml).

```
|- forall n c r x.
       nf_data n c r /\
       x IN ring_carrier (subfield_generated complex_ring {r 1})
       ==> algebra_trace
           (subfield_generated (subfield_generated complex_ring {r 1})
            {ring_0 (subfield_generated complex_ring {r 1})},
            subfield_generated complex_ring {r 1})
           I
           x =
           vsum (1..n) (\k. nf_embedding n r k x)
```

## Part XII. Prime factors of polynomial values

A classical theorem (Polya, Siegel), made effective by linear forms in
logarithms (Shorey and Tijdeman; see Y. Bugeaud, Linear Forms in Logarithms
and Applications, EMS 2018, section 3.5): for an integer polynomial f with
two distinct roots and a finite set S, only finitely many integers x have
f(x) <> 0 with all prime factors in S; equivalently, the greatest prime
factor of f(x) tends to infinity. Here in qualitative form through
SUPERELLIPTIC (m = 3): an S-smooth value is f(x) = c y^3 with c from a
finite set, and Y^3 = c^2 f(X) has only finitely many integer solutions;
for roots of any multiplicity, a factor of the monic scaling of f with two
distinct simple roots (built from the minimal polynomials of the two roots)
carries the smoothness over. A prime p divides the real integer v iff
v = &p * k for an integer k; there is no hypothesis on the leading
coefficient (the zero polynomial gives empty sets). Baker/make.ml section 19
(it needs ANT/ and sections 1 to 6, 11, 12 and 14).

### POLY_SMOOTH_VALUES_FINITE  (Baker/prime_factors.ml)
Two distinct roots of any multiplicity: only finitely many integers x have f(x) <> 0 with all prime factors in the finite set S.

```
|- forall N a z1 z2 S.
       (forall i. integer (a i)) /\
       ~(z1 = z2) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       FINITE S
       ==> FINITE
           {x | integer x /\
                ~(sum (0..N) (\i. a i * x pow i) = &0) /\
                (forall p.
                     prime p /\
                     (exists k.
                          integer k /\
                          sum (0..N) (\i. a i * x pow i) = &p * k)
                     ==> p IN S)}
```

### POLY_SMOOTH_VALUES_FINITE_SIMPLE  (Baker/prime_factors.ml)
The same for two distinct simple roots (the first step: f(x) = c y^3 with c from a finite set, and SUPERELLIPTIC with m = 3 for c^2 f).

```
|- forall N a z1 z2 S.
       (forall i. integer (a i)) /\
       ~(z1 = z2) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z1 pow (i - 1)) = Cx (&0)) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z2 pow (i - 1)) = Cx (&0)) /\
       FINITE S
       ==> FINITE
           {x | integer x /\
                ~(sum (0..N) (\i. a i * x pow i) = &0) /\
                (forall p.
                     prime p /\
                     (exists k.
                          integer k /\
                          sum (0..N) (\i. a i * x pow i) = &p * k)
                     ==> p IN S)}
```

### POLY_LARGEST_PRIME_FACTOR  (Baker/prime_factors.ml)
For a nonzero f, the greatest prime factor of its nonzero integer values
tends to infinity as |x| grows. The formal statement uses existence of a
prime divisor above B; it also includes the zero polynomial, since every
prime divides zero.

```
|- forall N a z1 z2 B.
       (forall i. integer (a i)) /\
       ~(z1 = z2) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0)
       ==> (exists X.
                forall x.
                    integer x /\ X <= abs x
                    ==> (exists p k.
                             prime p /\
                             B < p /\
                             integer k /\
                             sum (0..N) (\i. a i * x pow i) = &p * k))
```

### POLY_PRIME_POWER_VALUES_FINITE  (Baker/prime_factors.ml)
f(x) = +-p^n has only finitely many solutions (x, n), for any p >= 2.

```
|- forall N a z1 z2 p.
       (forall i. integer (a i)) /\
       ~(z1 = z2) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       2 <= p
       ==> FINITE
           {x,n | integer x /\
                  abs (sum (0..N) (\i. a i * x pow i)) = &p pow n}
```

### SQUARE_PLUS_SMOOTH_FINITE  (Baker/prime_factors.ml)
For D <> 0, x^2 + D has all its prime factors in S only finitely often.

```
|- forall D S.
       integer D /\ ~(D = &0) /\ FINITE S
       ==> FINITE
           {x | integer x /\
                ~(x pow 2 + D = &0) /\
                (forall p.
                     prime p /\ (exists k. integer k /\ x pow 2 + D = &p * k)
                     ==> p IN S)}
```

### SQUARE_PLUS_PRIME_POWER_FINITE  (Baker/prime_factors.ml)
For D <> 0 and p >= 2, x^2 + D = p^n has only finitely many solutions (the finiteness behind the Ramanujan-Nagell and Lebesgue-Nagell equations).

```
|- forall D p.
       integer D /\ ~(D = &0) /\ 2 <= p
       ==> FINITE {x,n | integer x /\ x pow 2 + D = &p pow n}
```

### LARGEST_PRIME_FACTOR_SQUARE_PLUS_1  (Baker/prime_factors.ml)
The greatest prime factor of n^2 + 1 tends to infinity.

```
|- forall B.
       exists M.
           forall n.
               M <= n
               ==> (exists p. prime p /\ B < p /\ p divides n EXP 2 + 1)
```

### INTEGER_SMOOTH_POW_DECOMPOSITION  (Baker/prime_factors.ml)
A non-zero integer whose prime factors lie in a finite set S is c y^m with c from a finite set of non-zero integers.

```
|- forall S m.
       FINITE S /\ 1 <= m
       ==> (exists C.
                FINITE C /\
                (forall c. c IN C ==> integer c /\ ~(c = &0)) /\
                (forall v.
                     integer v /\
                     ~(v = &0) /\
                     (forall p.
                          prime p /\ (exists k. integer k /\ v = &p * k)
                          ==> p IN S)
                     ==> (exists c y. c IN C /\ integer y /\ v = c * y pow m)))
```

## Part XIII. The Schinzel-Tijdeman theorem

A. Schinzel and R. Tijdeman (Acta Arith. 31, 1976), from Sharpening I for
algebraic numbers (Part II, SHARP_BAKER_NUMBER_FIELD): if f has integer
coefficients and two distinct complex roots, of any multiplicities, the
integer solutions of y^m = f(x) with |y| >= 2 have bounded m
(SCHINZEL_TIJDEMAN). Per root an S-unit descent with ANT/ gives
(x - theta)^k = prod v^(e v) xi^m with a fixed finite set of S-units v,
e v < m and D xi integral for a fixed D (SCHINZEL_TIJDEMAN_ROOT_DESCENT);
then one complex linear form for any two distinct roots, in the field
Q(Z1, Z2): no case split between real, complex or conjugate roots, no
hypothesis on the leading coefficient. With simple roots the solutions are
finitely many (SCHINZEL_TIJDEMAN_FINITE for m >= 3, the CARD form
SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS for m >= m0), and x^2 + D = y^n has
only finitely many solutions with |y| >= 2, n >= 2 for D <> 0
(SQUARE_PLUS_POW_FINITE). The reducible case is a corollary (Part VI).
Baker/make.ml section 20 (it needs ANT/ and sections 1 to 6, 11, 12, 14, 18
and 19); the S-unit descent (Baker/schinzel_sunit.ml) is in section 12,
where the descent NF_POWER_DESCENT rests on it too. The ANT theorems behind
the descent are listed at the end.

### SCHINZEL_TIJDEMAN  (Baker/schinzel_general.ml)
Two distinct complex roots of any multiplicities: the exponent m of y^m = f(x) with |y| >= 2 is bounded.

```
|- forall N a z1 z2.
       (forall i. integer (a i)) /\
       ~(z1 = z2) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0)
       ==> (exists M.
                forall x y m.
                    integer x /\
                    integer y /\
                    &2 <= abs y /\
                    y pow m = sum (0..N) (\i. a i * x pow i)
                    ==> m <= M)
```

### SCHINZEL_TIJDEMAN_FINITE  (Baker/schinzel_general.ml)
Two distinct simple roots: finitely many solutions (x, y, m) with |y| >= 2 and m >= 3.

```
|- forall N a z1 z2.
       (forall i. integer (a i)) /\
       ~(z1 = z2) /\
       vsum (0..N) (\i. Cx (a i) * z1 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z1 pow (i - 1)) = Cx (&0)) /\
       vsum (0..N) (\i. Cx (a i) * z2 pow i) = Cx (&0) /\
       ~(vsum (1..N) (\i. Cx (&i * a i) * z2 pow (i - 1)) = Cx (&0))
       ==> FINITE
           {x,y,m | integer x /\
                    integer y /\
                    &2 <= abs y /\
                    3 <= m /\
                    y pow m = sum (0..N) (\i. a i * x pow i)}
```

### SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS  (Baker/schinzel_general.ml)
The CARD form: at least two simple roots (three if m0 = 2) give finitely many solutions with m >= m0.

```
|- forall N a m0.
       2 <= m0 /\
       (forall i. integer (a i)) /\
       (if m0 = 2 then 3 else 2) <=
       CARD
       {z | vsum (0..N) (\i. Cx (a i) * z pow i) = Cx (&0) /\
            ~(vsum (1..N) (\i. Cx (&i * a i) * z pow (i - 1)) = Cx (&0))}
       ==> FINITE
           {x,y,m | integer x /\
                    integer y /\
                    &2 <= abs y /\
                    m0 <= m /\
                    y pow m = sum (0..N) (\i. a i * x pow i)}
```

### SQUARE_PLUS_POW_FINITE  (Baker/schinzel_general.ml)
For D <> 0, x^2 + D = y^n has only finitely many solutions with |y| >= 2 and n >= 2.

```
|- forall D.
       integer D /\ ~(D = &0)
       ==> FINITE
           {x,y,n | integer x /\
                    integer y /\
                    &2 <= abs y /\
                    2 <= n /\
                    x pow 2 + D = y pow n}
```

### SCHINZEL_TIJDEMAN_ROOT_DESCENT  (Baker/schinzel_sunit.ml)
The S-unit descent at a root theta = r 1 of c0 y^m = g(x)^k H(x): (x - theta)^k = prod_{v IN W} v^(e v) xi^m with e v < m, W and D independent of m, x, y, and D xi an algebraic integer (Baker/make.ml section 12; the general form SCHINZEL_TIJDEMAN_SUNIT_DESCENT of the same file is also the base of NF_POWER_DESCENT).

```
|- forall n c r k M H c0.
       nf_data n c r /\
       1 <= k /\
       (forall i. integer (H i)) /\
       ~(vsum (0..M) (\i. Cx (H i) * r 1 pow i) = Cx (&0)) /\
       integer c0 /\
       ~(c0 = &0)
       ==> (exists W D.
                FINITE W /\
                (forall v.
                     v IN W
                     ==> v IN
                         ring_carrier (subfield_generated complex_ring {r 1}) /\
                         ~(v = Cx (&0))) /\
                integer D /\
                &1 <= D /\
                (forall m x y.
                     1 <= m /\
                     integer x /\
                     integer y /\
                     ~(y = &0) /\
                     c0 * y pow m =
                     sum (0..n) (\i. c i * x pow i) pow k *
                     sum (0..M) (\i. H i * x pow i)
                     ==> (exists e xi.
                              (forall v. v IN W ==> e v < m) /\
                              xi IN
                              ring_carrier
                              (subfield_generated complex_ring {r 1}) /\
                              algebraic_integer (Cx D * xi) /\
                              (Cx x - r 1) pow k =
                              cproduct W (\v. v pow e v) * xi pow m)))
```

### The ANT theorems behind the S-unit descent

Eight theorems of ANT/ (Part XI) on which the S-unit descent rests:
denominators of ideals and of p-th roots (ANT/ideal_norm.ml,
ANT/dedekind_valuation.ml, ANT/nf_valuation.ml) and the m-th power
decomposition by S-units (ANT/sunits.ml).

### IDEAL_NORM_SUBSET_DIVIDES  (ANT/ideal_norm.ml)
The norm of an ideal divides the norm of every ideal of finite index inside it.

```
|- forall r j k.
       ring_ideal r j /\
       ring_ideal r k /\
       j SUBSET k /\
       FINITE (ring_carrier (quotient_ring r j))
       ==> ideal_norm r k divides ideal_norm r j
```

### DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS  (ANT/dedekind_valuation.ml)
In a Dedekind domain the nonzero ideals realize every finitely supported choice of valuations.

```
|- forall r f.
       dedekind_domain r /\
       FINITE {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ ~(f p = 0)}
       ==> (exists j.
                ring_ideal r j /\
                ~(j = {ring_0 r}) /\
                (forall p.
                     prime_ideal r p /\ ~(p = {ring_0 r})
                     ==> ideal_valuation r p j = f p))
```

### NUMBER_FIELD_DENOMINATOR_IDEAL  (ANT/nf_valuation.ml)
The denominator ideal of a nonzero element x: v_P(J) = max(0, -v_P(x)).

```
|- forall k x.
       number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
       ==> (exists J.
                ring_ideal (ring_of_integers k) J /\
                ~(J = {ring_0 k}) /\
                (forall P.
                     prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                     ==> &(ideal_valuation (ring_of_integers k) P J) =
                         max (&0)
                         (--dedekind_valuation (ring_of_integers k,k) I P x)))
```

### NUMBER_FIELD_IDEAL_MUL_INTEGRAL  (ANT/nf_valuation.ml)
An ideal J with v_P(J) + v_P(x) >= 0 everywhere clears the denominator of x.

```
|- forall k J x c.
       number_field k /\
       ring_ideal (ring_of_integers k) J /\
       x IN ring_carrier k /\
       (forall P.
            prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
            ==> &0 <=
                &(ideal_valuation (ring_of_integers k) P J) +
                dedekind_valuation (ring_of_integers k,k) I P x) /\
       c IN J
       ==> ring_mul k c x IN ring_carrier (ring_of_integers k)
```

### NUMBER_FIELD_ROOT_DENOMINATOR  (ANT/nf_valuation.ml)
Denominators of p-th roots (Baker and Stark 1971, Lemma 4): if a x^p is integral then so is b x with b^p <= N((a)).

```
|- forall k x a p.
       number_field k /\
       x IN ring_carrier k /\
       a IN ring_carrier (ring_of_integers k) /\
       ~(a = ring_0 k) /\
       ring_mul k a (ring_pow k x p) IN ring_carrier (ring_of_integers k)
       ==> (exists b.
                1 <= b /\
                b EXP p <=
                ideal_norm (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {a}) /\
                ring_mul k (ring_of_num k b) x IN
                ring_carrier (ring_of_integers k))
```

### S_UNIT_GROUP_SUM  (ANT/sunits.ml)
Products in the S-unit group are products in the field.

```
|- forall k S s f.
       FINITE s /\
       (forall i. i IN s ==> f i IN group_carrier (s_unit_group k S))
       ==> group_sum (s_unit_group k S) s f = ring_product k s f
```

### S_UNIT_GROUP_GENERATORS_MOD_POW  (ANT/sunits.ml)
One finite set of S-units generates the S-units modulo m-th powers for every m, with exponents below m.

```
|- forall k S.
       number_field k /\ FINITE S
       ==> (exists t.
                FINITE t /\
                t SUBSET group_carrier (s_unit_group k S) /\
                (forall m x.
                     ~(m = 0) /\ x IN group_carrier (s_unit_group k S)
                     ==> (exists n y.
                              (forall v. n v < m) /\
                              y IN group_carrier (s_unit_group k S) /\
                              x =
                              ring_mul k
                              (ring_product k t (\v. ring_pow k v (n v)))
                              (ring_pow k y m))))
```

### NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION  (ANT/sunits.ml)
A finite set t of primes such that every x with m | v_P(x) outside S is an (S UNION t)-unit times an m-th power.

```
|- forall k.
       number_field k
       ==> (exists t.
                FINITE t /\
                (forall S m x.
                     x IN ring_carrier k /\
                     ~(x = ring_0 k) /\
                     (forall P.
                          prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k}) /\
                          ~(P IN S)
                          ==> &m divides
                              dedekind_valuation (ring_of_integers k,k) I P x)
                     ==> (exists y u.
                              y IN ring_carrier k /\
                              ~(y = ring_0 k) /\
                              u IN group_carrier (s_unit_group k (S UNION t)) /\
                              x = ring_mul k u (ring_pow k y m))))
```

## Part XIV. Perfect powers in Lucas sequences, x^k + D = y^n

Applications of the Schinzel-Tijdeman theorem (Part XIII). A Lucas
sequence u_0 = 0, u_1 = 1, u_(n+2) = P u_(n+1) - Q u_n with Q = +-1 and
P^2 <> 4 Q contains only finitely many perfect powers y^m with |y| >= 2,
m >= 2, and so does its companion v_0 = 2, v_1 = P for every P: the case
alpha beta = +-1 of the theorem of A. Petho (J. Number Theory 15, 1982) and
T. N. Shorey and C. L. Stewart (Math. Scand. 52, 1983) on perfect powers in
binary recurrences (Y. Bugeaud, Linear Forms in Logarithms and
Applications, EMS 2018, Theorem 6.12). Hence the Fibonacci, Pell and Lucas
numbers contain only finitely many perfect powers; the exact lists (0, 1,
8, 144 and 1, 4: Bugeaud, Mignotte and Siksek, Ann. of Math. 163, 2006)
need modular methods and are not formalized. Route: the invariant
u_(n+1)^2 - P u_(n+1) u_n + Q u_n^2 = Q^n turns u_n = y^m into
X^2 + C = Delta y^(2m) with X = 2 u_(n+1) - P u_n, Delta = P^2 - 4 Q and
C = -4 Q^n = +-4 (C = +-4 Delta for v_n); for x^2 + C = D y^n the monic
form SCHINZEL_TIJDEMAN_GENERAL_MONIC bounds n and SUPERELLIPTIC_MONIC
handles each n (with Y = D y); the growth |u_n| >= (n - 1)/2 for
|P| >= Q + 2 bounds n, and the remaining sequences (Q = 1, |P| <= 1;
Q = -1, P = 0) are periodic with |u_n| <= 1, |v_n| <= 2. No residue
classes are needed. With the k simple roots of x^k + D,
SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS gives the finiteness of
x^k + D = y^n for each fixed k (with k varying too this is the conjecture
of Pillai). Each hypothesis is necessary: P^2 = 4 Q (u_n = n), Q = -4
(u_(2j+1) = 4^j), n = 2 in x^2 + 1 = 2 y^n (a Pell equation), k = 1 and
D = 0 give infinite sets. Baker/make.ml section 21 (it needs sections 12, 19
and 20 and Examples/gcdrecurrence.ml).

### LUCAS_PERFECT_POWERS_FINITE  (Baker/perfect_powers.ml)
Lucas sequences U(P, Q) with Q = +-1 and P^2 <> 4 Q: only finitely many terms are perfect powers y^m with |y| >= 2, m >= 2 (for P^2 = 4 Q the sequence is u_n = +-n).

```
|- forall P Q u.
       integer P /\
       (Q = &1 \/ Q = -- &1) /\
       ~(P pow 2 = &4 * Q) /\
       u 0 = &0 /\
       u 1 = &1 /\
       (forall n. u (n + 2) = P * u (n + 1) - Q * u n)
       ==> FINITE
           {n,y,m | integer y /\ &2 <= abs y /\ 2 <= m /\ u n = y pow m}
```

### LUCAS_COMPANION_PERFECT_POWERS_FINITE  (Baker/perfect_powers.ml)
The companion sequences V(P, Q) (v_0 = 2, v_1 = P) with Q = +-1: the same, for every integer P.

```
|- forall P Q v.
       integer P /\
       (Q = &1 \/ Q = -- &1) /\
       v 0 = &2 /\
       v 1 = P /\
       (forall n. v (n + 2) = P * v (n + 1) - Q * v n)
       ==> FINITE
           {n,y,m | integer y /\ &2 <= abs y /\ 2 <= m /\ v n = y pow m}
```

### FIBONACCI_PERFECT_POWERS_FINITE  (Baker/perfect_powers.ml)
Petho (1982), Shorey and Stewart (1983): only finitely many Fibonacci numbers are perfect powers (fib of Examples/gcdrecurrence.ml).

```
|- FINITE {n,y,m | 2 <= m /\ 2 <= y /\ fib n = y EXP m}
```

### PELL_PERFECT_POWERS_FINITE  (Baker/perfect_powers.ml)
The Pell numbers 0, 1, 2, 5, 12, 29, ... contain only finitely many perfect powers.

```
|- forall u.
       u 0 = 0 /\ u 1 = 1 /\ (forall n. u (n + 2) = 2 * u (n + 1) + u n)
       ==> FINITE {n,y,m | 2 <= m /\ 2 <= y /\ u n = y EXP m}
```

### LUCAS_NUMBERS_PERFECT_POWERS_FINITE  (Baker/perfect_powers.ml)
The Lucas numbers 2, 1, 3, 4, 7, 11, ... contain only finitely many perfect powers.

```
|- forall v.
       v 0 = 2 /\ v 1 = 1 /\ (forall n. v (n + 2) = v (n + 1) + v n)
       ==> FINITE {n,y,m | 2 <= m /\ 2 <= y /\ v n = y EXP m}
```

### LUCAS_NUM_PERFECT_POWERS_FINITE  (Baker/perfect_powers.ml)
Every sequence u_(n+2) = p u_(n+1) + u_n with u_0 = 0, u_1 = 1 (the num form of Q = -1).

```
|- forall p u.
       u 0 = 0 /\ u 1 = 1 /\ (forall n. u (n + 2) = p * u (n + 1) + u n)
       ==> FINITE {n,y,m | 2 <= m /\ 2 <= y /\ u n = y EXP m}
```

### POW_PLUS_POW_FINITE  (Baker/perfect_powers.ml)
For fixed k >= 2 and D <> 0, x^k + D = y^n has only finitely many integer solutions with |y| >= 2 and n >= 2 (k = 2 is SQUARE_PLUS_POW_FINITE).

```
|- forall k D.
       2 <= k /\ integer D /\ ~(D = &0)
       ==> FINITE
           {x,y,n | integer x /\
                    integer y /\
                    &2 <= abs y /\
                    2 <= n /\
                    x pow k + D = y pow n}
```

### SQUARE_PLUS_MUL_POW_FINITE  (Baker/perfect_powers.ml)
For C, D <> 0, x^2 + C = D y^n has only finitely many solutions with |y| >= 2 and n >= 3 (for n = 2 it is a Pell equation).

```
|- forall C D.
       integer C /\ integer D /\ ~(C = &0) /\ ~(D = &0)
       ==> FINITE
           {x,y,n | integer x /\
                    integer y /\
                    &2 <= abs y /\
                    3 <= n /\
                    x pow 2 + C = D * y pow n}
```

## Part XV. Imaginary quadratic fields of class number two

Baker (Ann. of Math. 94, 1971) and Stark (Ann. of Math. 94, 1971) proved
that only finitely many imaginary quadratic fields have class number two;
the list of the eighteen fields was completed by Montgomery and Weinberger
(Acta Arith. 24, 1974) and Stark (Math. Comp. 29, 1975). Here the route of
Baker (Transcendental Number Theory, Ch. 5, sec. 5) with the class number of
Gauss (form_classno, the number of reduced primitive forms, as in Part VII):
only finitely many squarefree d have form_classno (qdisc d) = 2
(CLASS_NUMBER_TWO_FINITE; CLASS_NUMBER_TWO_FINITE_ODD for the discriminants
-d), and the eighteen known d do (CLASS_NUMBER_TWO_EXAMPLES; that there are
no others is not formalized). Genus theory by witness forms
(CN_FORMS_TWO_CASES) leaves d = p q with primes p = 1, q = 3 mod 4
(d = 3 mod 8 or d = 15), a prime d = 1 mod 4 and d = 2 p (discriminant -4d);
in the first case the genus character is (q | p) = -1 (CN_GENUS_CHARACTER,
by Dirichlet's theorem on primes in progressions). An elementary two-lattice
local analysis gives the representation numbers of the two classes of forms
(CN_REP_TOTAL_ODD, CN_REP_GENUS_ODD, CN_REP_TOTAL_EVEN). The limit formula
for a general positive definite form and a general modulus k = k1 k2
(QFORM_SLICE_BOUND, with the Ramanujan identity QFORM_LIMIT_RAMANUJAN) and
the lattice series (QFORM_DIRICHLET_SERIES) of the general form layer of
section 15, shared with the class number one problem (Baker/qform_limit.ml,
Baker/qform_series.ml), give the genus identity L(1,chi_k)
L(1,chi_kd) + L(1,chi_kp) L(1,chi_kq) = 2 (zeta_k(2) + S) with the slice sum
S of the principal form alone (CN_GENUS_PRODUCT_LIMIT) and two total
identities (CN_TOTAL_PRODUCT_LIMIT, CN_TOTAL_PRODUCT_LIMIT_EVEN). The class
number formulas in absolute value (Part VII, and CN_L1_KCHAR4 for the odd
characters of even modulus), the cyclotomic unit lemma
(CN_CYCLO_UNIT_QUADRATIC: cyclo_unit q lies in Q(sqrt q) and is a root of
X^2 - t X + 1), |L(1,chi)| <= log m + 3 (CN_L1_BOUND) and zeta(2) = pi^2/6
(CN_ZETA_2) turn these into linear forms in logarithms. For d = p q with
q^4 > d: the form b1 log eps_21 + b2 log xi_21p - (128/7) pi sqrt d of size
at most 504 qform_kernel(exp(-pi sqrt(d)/21)) (CN_LINEAR_MAIN), with one
number xi_21p of large height and the algebraic coefficient (128/7) i sqrt d
on log(-1) = i pi, closed by BAKER_SHARPENING_ALGEBRAIC_COEFFS (Part II,
n = 3, degree 2): no fundamental units and no class numbers h(21 p) are
needed. For q^4 <= d and for the discriminants -4d: two-log forms in the
fixed numbers cyclo_unit k and -1 with an algebraic coefficient
(CN_LINEAR_SMALL with k = 21, 33 or 77; CN_LINEAR_EVEN with k = 21), closed
by BAKER_FELDMAN. The forms never vanish, by Gelfond-Schneider.
Baker/make.ml section 22 (it needs ANT/ and sections 1 to 7, 9 to 11, 13 and
15).

### CLASS_NUMBER_TWO_FINITE  (Baker/cn_main.ml)
Baker 1971, Stark 1971: only finitely many squarefree d give the discriminant of Q(sqrt(-d)) exactly two reduced primitive forms, i.e. class number two in the sense of Gauss.

```
|- FINITE {d | squarefree d /\ form_classno (qdisc d) = 2}
```

### CLASS_NUMBER_TWO_FINITE_ODD  (Baker/cn_main.ml)
The odd discriminants -d, d = 3 mod 4.

```
|- FINITE {d | squarefree d /\ d MOD 4 = 3 /\ form_classno (-- &d) = 2}
```

### CLASS_NUMBER_TWO_EXAMPLES  (Baker/cn_forms.ml)
The eighteen known fields (by an evaluator that finds the two reduced primitive forms).

```
|- forall d.
       d IN
       {5, 6, 10, 13, 15, 22, 35, 37, 51, 58, 91, 115, 123, 187, 235, 267,
        403, 427}
       ==> form_classno (qdisc d) = 2
```

### CN_FORMS_TWO_CASES  (Baker/cn_forms.ml)
Genus theory for class number two by witnesses.

```
|- forall d.
       squarefree d /\ form_classno (qdisc d) = 2
       ==> (exists p q.
                prime p /\
                prime q /\
                p MOD 4 = 1 /\
                q MOD 4 = 3 /\
                d = p * q /\
                (d MOD 8 = 3 \/ d = 15)) \/
           prime d /\ d MOD 4 = 1 \/
           (exists p. prime p /\ ODD p /\ d = 2 * p)
```

### CN_GENUS_CHARACTER  (Baker/cn_forms.ml)
The genus character of the second class: (q | p) = -1.

```
|- forall p q.
       prime p /\
       prime q /\
       p MOD 4 = 1 /\
       q MOD 4 = 3 /\
       form_classno (-- &(p * q)) = 2
       ==> qchar p q = -- &1
```

### CN_REP_TOTAL_ODD  (Baker/cn_rep.ml)
The representation numbers of the two forms f = (1, 1, (d + 1)/4) and f2 = (q, q, (p + q)/4) of discriminant -d, d = p q: the total.

```
|- forall p q l.
       prime p /\
       prime q /\
       p MOD 4 = 1 /\
       q MOD 4 = 3 /\
       form_classno (-- &(p * q)) = 2 /\
       1 <= l
       ==> &(qform_rep (&1) (&1) (&((p * q + 1) DIV 4)) l) +
           &(qform_rep (&q) (&q) (&((p + q) DIV 4)) l) =
           &2 * sum {m | m divides l} (\m. qchar (p * q) m)
```

### CN_REP_GENUS_ODD  (Baker/cn_rep.ml)
The difference: the genus character (m | p) (l/m | q).

```
|- forall p q l.
       prime p /\
       prime q /\
       p MOD 4 = 1 /\
       q MOD 4 = 3 /\
       form_classno (-- &(p * q)) = 2 /\
       1 <= l
       ==> &(qform_rep (&1) (&1) (&((p * q + 1) DIV 4)) l) -
           &(qform_rep (&q) (&q) (&((p + q) DIV 4)) l) =
           &2 * sum {m | m divides l} (\m. qchar p m * qchar q (l DIV m))
```

### CN_REP_TOTAL_EVEN  (Baker/cn_rep_even.ml)
The two forms of discriminant -4d (d a prime = 1 mod 4 or d = 2 p): the total, with the Kronecker symbol kchar4 d = (-4d / .).

```
|- forall d l.
       (prime d /\ d MOD 4 = 1 \/ (exists p. prime p /\ ODD p /\ d = 2 * p)) /\
       form_classno (--(&4 * &d)) = 2 /\
       1 <= l
       ==> &(qform_rep (&1) (&0) (&d) l) +
           &(qform_rep (&2) (if d MOD 4 = 1 then &2 else &0)
             (if d MOD 4 = 1 then &((d + 1) DIV 2) else &(d DIV 2))
            l) =
           &2 * sum {m | m divides l} (\m. kchar4 d m)
```

### QFORM_LIMIT_RAMANUJAN  (Baker/qform_limit.ml)
The Ramanujan identity for a general form: the sum of chi_k(F(m,y)) over m < k is chi_k(a) times the Ramanujan sum c_k(y) (the general form layer of Baker/make.ml section 15).

```
|- forall k k1 k2 a b c y.
       k = k1 * k2 /\
       prime k1 /\
       prime k2 /\
       ~(k1 = k2) /\
       ODD k /\
       &0 < a /\
       &0 < &4 * a * c - b pow 2 /\
       coprime (k,num_of_int a) /\
       coprime (k,num_of_int (&4 * a * c - b pow 2))
       ==> sum (0..k - 1) (\m. qchar k (num_of_int (qform a b c (&m) (&y)))) =
           qchar k (num_of_int a) *
           (&1 -
            &k1 * (if k1 divides y then &1 else &0) -
            &k2 * (if k2 divides y then &1 else &0) +
            &k * (if k divides y then &1 else &0))
```

### QFORM_SLICE_BOUND  (Baker/qform_limit.ml)
The limit formula for a general positive definite form F = (a,b,c) and k = k1 k2: the slice sum is exponentially small, without a class number hypothesis (CLASSNO_SLICE_BOUND of Part VII is a special case).

```
|- forall k k1 k2 a b c S.
       k = k1 * k2 /\
       prime k1 /\
       prime k2 /\
       ~(k1 = k2) /\
       ODD k /\
       &0 < a /\
       &0 < &4 * a * c - b pow 2 /\
       coprime (k,num_of_int a) /\
       coprime (k,num_of_int (&4 * a * c - b pow 2)) /\
       (qform_slice k a b c (&1) real_sums S) (from 1)
       ==> abs S <=
           &4 *
           pi / sqrt (real_of_int (&4 * a * c - b pow 2)) *
           qform_kernel
           (exp
           (--(pi *
               sqrt (real_of_int (&4 * a * c - b pow 2)) /
               (real_of_int a * &k))))
```

### QFORM_DIRICHLET_SERIES  (Baker/qform_series.ml)
The lattice series of a general form for s > 1: the row y = 0 and twice the slices.

```
|- forall k a b c s.
       &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 < s
       ==> ((\l. qchar k l * &(qform_rep a b c l) / &l rpow s) real_sums
            &2 *
            qchar k (num_of_int a) / real_of_int a rpow s *
            real_infsum (from 1)
            (\n. if coprime (n,k) then inv ((&n pow 2) rpow s) else &0) +
            &2 * real_infsum (from 1) (qform_slice k a b c s))
           (from 1)
```

### CN_GENUS_PRODUCT_LIMIT  (Baker/cn_products.ml)
The genus identity at s = 1 (Baker, TNT Ch. 5 sec. 5): only the slice sum of the principal form remains.

```
|- forall k k1 k2 p q.
       k = k1 * k2 /\
       prime k1 /\
       prime k2 /\
       ~(k1 = k2) /\
       k MOD 4 = 1 /\
       prime p /\
       prime q /\
       p MOD 4 = 1 /\
       q MOD 4 = 3 /\
       coprime (k,p * q) /\
       form_classno (-- &(p * q)) = 2
       ==> (exists S.
                (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) (&1) real_sums
                 S)
                (from 1) /\
                Lfunction (\n. Cx (qchar k n)) *
                Lfunction (\n. Cx (qchar (k * p * q) n)) +
                Lfunction (\n. Cx (qchar (k * p) n)) *
                Lfunction (\n. Cx (qchar (k * q) n)) =
                Cx (&2 * (zeta_coprime k + S)))
```

### CN_TOTAL_PRODUCT_LIMIT  (Baker/cn_products.ml)
The total identity for the two forms of discriminant -d.

```
|- forall k k1 k2 p q.
       k = k1 * k2 /\
       prime k1 /\
       prime k2 /\
       ~(k1 = k2) /\
       k MOD 4 = 1 /\
       prime p /\
       prime q /\
       p MOD 4 = 1 /\
       q MOD 4 = 3 /\
       coprime (k,p * q) /\
       form_classno (-- &(p * q)) = 2
       ==> (exists S1 S2.
                (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) (&1) real_sums
                 S1)
                (from 1) /\
                (qform_slice k (&q) (&q) (&((p + q) DIV 4)) (&1) real_sums
                 S2)
                (from 1) /\
                Lfunction (\n. Cx (qchar k n)) *
                Lfunction (\n. Cx (qchar (k * p * q) n)) =
                Cx (zeta_coprime k * (&1 + qchar k q / &q) + S1 + S2))
```

### CN_TOTAL_PRODUCT_LIMIT_EVEN  (Baker/cn_products.ml)
The total identity for the two forms of discriminant -4d.

```
|- forall k k1 k2 d.
       k = k1 * k2 /\
       prime k1 /\
       prime k2 /\
       ~(k1 = k2) /\
       k MOD 4 = 1 /\
       (prime d /\ d MOD 4 = 1 \/ (exists p. prime p /\ ODD p /\ d = 2 * p)) /\
       coprime (k,d) /\
       form_classno (--(&4 * &d)) = 2
       ==> (exists b2 c2 S1 S2.
                &8 * c2 - b2 pow 2 = &4 * &d /\
                (qform_slice k (&1) (&0) (&d) (&1) real_sums S1) (from 1) /\
                (qform_slice k (&2) b2 c2 (&1) real_sums S2) (from 1) /\
                Lfunction (\n. Cx (qchar k n)) *
                Lfunction (\n. Cx (qchar k n * kchar4 d n)) =
                Cx (zeta_coprime k * (&1 + qchar k 2 / &2) + S1 + S2))
```

### CN_CYCLO_UNIT_QUADRATIC  (Baker/cn_cyclo.ml)
The cyclotomic unit of a real quadratic field of composite discriminant q lies in Q(sqrt q) and is a root of X^2 - t X + 1 (Gauss sums and the Galois group of Q(zeta_q) inside C, ANT/cyclotomic_galois.ml; Phi_q(1) = 1 from ANT/cyclotomic_poly.ml).

```
|- forall q.
       squarefree q /\ q MOD 4 = 1 /\ 1 < q /\ ~prime q
       ==> (exists t u v.
                integer t /\
                rational u /\
                rational v /\
                cyclo_unit q = u + v * sqrt (&q) /\
                cyclo_unit q pow 2 - t * cyclo_unit q + &1 = &0)
```

### CN_L1_BOUND  (Baker/cn_cyclo.ml)
|L(1,c)| <= log m + 3 for every nonprincipal Dirichlet character c modulo m.

```
|- forall m c.
       1 <= m /\ dirichlet_character m c /\ ~(c = chi_0 m)
       ==> norm (Lfunction c) <= log (&m) + &3
```

### KCHAR4_DIRICHLET  (Baker/cn_gauss_even.ml)
kchar4 d = (-4d / .) is a Dirichlet character modulo 4 d.

```
|- forall d.
       d MOD 4 = 1 \/ d MOD 4 = 2
       ==> dirichlet_character (4 * d) (\n. Cx (kchar4 d n))
```

### CN_L1_KCHAR4  (Baker/cn_gauss_even.ml)
The class number formula in absolute value for the odd characters chi_k kchar4 d of even modulus: |L(1,chi)| = pi |t| / (2 sqrt(k d)) with an integer t.

```
|- forall k d.
       squarefree (k * d) /\
       k MOD 4 = 1 /\
       (d MOD 4 = 1 \/ d MOD 4 = 2) /\
       1 < k * d
       ==> (exists t.
                integer t /\
                norm (Lfunction (\n. Cx (qchar k n * kchar4 d n))) =
                pi * abs t / (&2 * sqrt (&(k * d))))
```

### CN_ZETA_2  (Baker/cn_zeta.ml)
zeta(2) = pi^2/6 (from the Poisson kernel identity, without power series).

```
|- zeta_coprime 1 = pi pow 2 / &6
```

### CN_LINEAR_MAIN  (Baker/cn_linear.ml)
The class number two linear form (k = 21): b1 log eps + b2 log xi - (128/7) pi sqrt(p q) is exponentially small, with explicit bounds for the integers b1, b2.

```
|- forall p q.
       prime p /\
       prime q /\
       p MOD 4 = 1 /\
       q MOD 4 = 3 /\
       (p * q) MOD 8 = 3 /\
       coprime (21,p * q) /\
       form_classno (-- &(p * q)) = 2
       ==> (exists b1 b2.
                integer b1 /\
                integer b2 /\
                ~(b1 = &0) /\
                ~(b2 = &0) /\
                abs b1 <=
                &2 * sqrt (&(21 * p * q)) * (log (&(21 * p * q)) + &3) /\
                abs b2 <= sqrt (&(21 * q)) * (log (&(21 * q)) + &3) /\
                abs
                (b1 * log ((&5 + sqrt (&21)) / &2) +
                 b2 * log (cyclo_unit (21 * p)) -
                 &128 / &7 * pi * sqrt (&(p * q))) <=
                &504 * qform_kernel (exp (--(pi * sqrt (&(p * q)) / &21))))
```

### CN_LINEAR_SMALL  (Baker/cn_linear.ml)
The two classes with small q: a two-log form in log(cyclo_unit k) and pi with a rational multiple of sqrt(d).

```
|- forall k k1 k2 p q.
       k = k1 * k2 /\
       prime k1 /\
       prime k2 /\
       ~(k1 = k2) /\
       k MOD 4 = 1 /\
       prime p /\
       prime q /\
       p MOD 4 = 1 /\
       q MOD 4 = 3 /\
       coprime (k,p * q) /\
       form_classno (-- &(p * q)) = 2
       ==> (exists b u.
                integer b /\
                ~(b = &0) /\
                (u = &1 \/ u = &3) /\
                abs b <= &q * sqrt (&(k * p * q)) * (log (&(k * p * q)) + &3) /\
                abs
                (b * log (cyclo_unit k) -
                 u *
                 (&q + qchar k q) *
                 &((k1 EXP 2 - 1) * (k2 EXP 2 - 1)) / (&6 * &k) *
                 pi *
                 sqrt (&(p * q))) <=
                &4 *
                u *
                &q *
                &k *
                (qform_kernel (exp (--(pi * sqrt (&(p * q)) / &k))) +
                 qform_kernel (exp (--(pi * sqrt (&(p * q)) / (&q * &k))))))
```

### CN_LINEAR_EVEN  (Baker/cn_linear.ml)
The discriminants -4d: the same with the even-modulus class number formula.

```
|- forall k k1 k2 d.
       k = k1 * k2 /\
       prime k1 /\
       prime k2 /\
       ~(k1 = k2) /\
       k MOD 4 = 1 /\
       (prime d /\ d MOD 4 = 1 \/ (exists p. prime p /\ ODD p /\ d = 2 * p)) /\
       coprime (k,d) /\
       form_classno (--(&4 * &d)) = 2
       ==> (exists b.
                integer b /\
                ~(b = &0) /\
                abs b <= &2 * sqrt (&(k * d)) * (log (&(4 * k * d)) + &3) /\
                abs
                (b * log (cyclo_unit k) -
                 (&2 + qchar k 2) *
                 &((k1 EXP 2 - 1) * (k2 EXP 2 - 1)) / (&3 * &k) *
                 pi *
                 sqrt (&d)) <=
                &8 *
                &k *
                (qform_kernel (exp (--(&2 * pi * sqrt (&d) / &k))) +
                 qform_kernel (exp (--(pi * sqrt (&d) / &k)))))
```

### The definitions  (Baker/cn_defs.ml)
The cyclotomic unit and the Kronecker symbol of -4d (Baker/cn_defs.ml), with the binary quadratic forms over the integers and their representation numbers (Baker/classno_defs.ml, section 5), the lattice terms and slices of a form twisted by chi_k = qchar k and the error kernel (Baker/classno_chardefs.ml, section 15), as printed by HOL.

```
|- forall a b x c y. qform a b c x y = a * x pow 2 + b * x * y + c * y pow 2
|- forall a b c l. qform_rep a b c l = CARD {x,y | qform a b c x y = &l}
|- forall k a b c x y s.
       qform_term k a b c s x y =
       qchar k (num_of_int (qform a b c x y)) /
       real_of_int (qform a b c x y) rpow s
|- forall k a b c s y.
       qform_slice k a b c s y =
       real_infsum (from 0)
       (\n.
            qform_term k a b c s (&n) (&y) +
            qform_term k a b c s (-- &n - &1) (&y))
|- forall q.
       cyclo_unit q =
       exp (--sum (1..q - 1) (\a. qchar q a * log (sin (pi * &a / &q))))
|- forall d m.
       kchar4 d m =
       (if EVEN m
        then &0
        else -- &1 pow ((m - 1) DIV 2) * real_of_int (jacobi (d,m)))
|- forall x. qform_kernel x = x * (&1 + x) / (&1 - x) pow 3
```

## File map (Baker/make.ml sections, in load order)

1. Library-style lemmas: generic lemmas shared by all sections. Needs only the library.
   - Baker/lemmas.ml                 Generic lemmas shared by several parts of the development.

2. Foundations: algebraic numbers, integer polynomials, Liouville and Siegel lemmas, Feldman polynomials, residues and interpolation, exponential polynomials, the bridge to algebraic_number, a lower bound for the roots of integer polynomials. Needs only section 1.
   - Baker/prelim.ml                 Preliminaries for Baker theorem: complex integers and small sums.
   - Baker/algebraic.ml              Polynomials over C: factorization, Newton identities, power sums.
   - Baker/intpoly.ml                Integer polynomial expressions in several complex variables.
   - Baker/liouville_inequality.ml   Liouville inequality for integer polynomials in algebraic numbers.
   - Baker/siegel.ml                 Siegel lemma, over the integers and for algebraic coefficients.
   - Baker/delta.ml                  Feldman Delta-functions, basis polynomials and common multiples.
   - Baker/residue.ml                Taylor expansion, residues on circles and the interpolation bound.
   - Baker/expoly.ml                 Uniqueness of exponential polynomials; polynomials of distinct degrees.
   - Baker/bridge.ml                 Bridge between algebraic_number and explicit integer polynomials.
   - Baker/simple.ml                 A lower bound for the nonzero roots of an integer polynomial.

3. Baker core (Baker, Transcendental Number Theory, Ch. 3): the auxiliary function, its arithmetic, extrapolation, section 4, the parametric core, the numeric layer and the explicit, existential and uniform core lower bounds. Needs only sections 1 and 2.
   - Baker/auxiliary.ml              The auxiliary function of Baker in single-variable form.
   - Baker/aux_arith.ml              Arithmetic of the auxiliary function: Baker Lemmas 4, 5 and 7.
   - Baker/extrap.ml                 The extrapolation argument: Baker Lemmas 6 and 7, analytic part.
   - Baker/sec4.ml                   The final step of Baker, Ch. 3, sec. 4: an integer relation.
   - Baker/bounds.ml                 Exp-form bounds for the auxiliary function and the Liouville bound.
   - Baker/parametric_core.ml        The parametric core of the Baker method.
   - Baker/estimates.ml              Explicit logarithmic estimates for the bound functions of Baker/parametric_core.ml.
   - Baker/param.ml                  The numeric layer of the Baker method: explicit parameters.
   - Baker/heights.ml                Degrees and heights at a point with m extra algebraic coordinates.
   - Baker/numeric_dmax.ml           The numeric core for an upper bound of the degree product.
   - Baker/explicit.ml               The core lower bound: explicit, existential and uniform versions.

4. Baker theorems and applications: BAKER_FELDMAN (Thm 3.1), linear independence of logarithms, Gelfond-Schneider, transcendence and irrationality measures, S-unit gaps, uniform bounds for possibly dependent logarithms (BAKER_UNIFORM_INTEGER, BAKER_UNIFORM_RATIONAL) and the uniform core with algebraic coefficients (the coefficient data sharpc_coefdata, BAKER_CORE_UNIFORM_ALGCOEFF; BAKER_CORE_UNIFORM_INTEGER is its instance for integer coefficients), examples. Needs only sections 1 to 3.
   - Baker/theorem.ml                Baker theorem on linear forms in logarithms: the effective lower bounds.
   - Baker/apps.ml                   Applications of Baker theorem: transcendence, Gelfond-Schneider, gaps between S-units, an ...
   - Baker/uniform.ml                Uniform lower bounds for arbitrary (possibly dependent) logarithms.
   - Baker/apps_examples.ml          Examples: the Baker theorems applied to specific numbers and to Diophantine equations.

5. Algebraic integers and number fields inside C: algebraic_integer (the integral elements of C over Z of ANT/integral.ml; closure under the ring operations, rational algebraic integers are integers, integer coefficients from integer power sums), the rings of integers of the subfields of C, the prime subfield Q, finitely many algebraic numbers generate a number field (NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED), subrings, subfields and homomorphisms of subfields of C. At its end the imaginary quadratic base files: the definitions of the binary quadratic forms and of qdisc (Baker/classno_defs.ml), the field Q(sqrt(-d)) as a number field of ANT/ with discriminant qdisc d (IMAG_QUADRATIC_FIELD_DISCRIMINANT), its ring of integers Z[omega] (IMAG_QUADRATIC_INTEGERS_CARRIER), the units, and the Euclidean algorithm for d = 1, 2, 3, 7, 11 (IMAG_QUADRATIC_INTEGERS_EUCLIDEAN, _PID, _UFD). Needs ANT/ and sections 1 and 2.
   - Baker/algint.ml                 Algebraic integers.
   - Baker/ant_bridge_complex.ml     Number fields inside the complex numbers: the bridge between ANT/, 100/transcendence.ml and the ...
   - Baker/classno_defs.ml           The class number one problem: binary quadratic forms and the class number of Gauss (definitions).
   - Baker/quadint_defs.ml           The ring of integers of an imaginary quadratic field: definitions.
   - Baker/quadint_ant.ml            The field Q(sqrt(-d)) inside the complex numbers as a number field of ANT/: its ring of integers, ...
   - Baker/quadint_ring.ml           The ring of integers of Q(sqrt(-d)): the carrier Z[omega], the units, the Euclidean algorithm for d ...

6. Sharpening I (Baker 1972) for algebraic numbers, uniform in the data: the machinery for integer and algebraic coefficients and the ending for integer coefficients. BAKER_SHARPENING (non-zero algebraic numbers of degree at most d, the first n - 1 of height at most exp g0, the last of height at most A, principal logarithms, integer coefficients of size at most B: Lambda = 0 or |Lambda| >= exp(-C g0^K log A log B), C and K depending only on n and d), BAKER_SHARPENING_REAL, SHARP_BAKER_NUMBER_FIELD (fixed numbers of a number field and one variable number with bounded denominator and conjugates), SHARP_BAKER_ALGEBRAIC. One machinery with complex coefficients bb r (integer coefficients are coefficient data of degree 1, SHARPC_COEFDATA_INTEGER): Delta-functions and the auxiliary function, Kummer theory over any subfield of C (KUMMER_COMPLEX, from the Kummer theory of Library/galois.ml), Lemmas 5, 6 and 8 over a Delta representation (sharp_deltarep: the integer values of the Baker binomial trick, SHARP_DELTAREP_INT, or the factorial polynomials of Baker 1973, SHARP_DELTAREP_ALG), section 4 over Q(alphas, betas), the extrapolation and one parametric core (SHARP_CORE_PARAMETRIC), the numeric design (SHARP_CORE_DESIGN, the design facts of both endings) with the numeric ending for integer coefficients (SHARP_CORE_ALGEBRAIC: log B), number field tools (denominators of p-th roots by the ideal norms of ANT/, degrees, integer polynomials of elements with bounded conjugates), the uniform base of both endings (BAKER_UNIFORM_ALGCOEFF, SHARPC_UNIFORM_ALG, with SHARP_UNIFORM_ALG as its instance), the shared descent tools and the descent for integer coefficients. Needs ANT/ and sections 1 to 5.
   - Baker/sharp_poly.ml             Sharpening I: Delta-functions and polynomial lemmas.
   - Baker/sharp_defs.ml             Sharpening I (Baker 1972, 1973): the definitions of the machinery.
   - Baker/sharp_aux.ml              Sharpening I: the auxiliary function.
   - Baker/kummer.ml                 Kummer theory for complex radicals over an arbitrary subfield s of C.
   - Baker/sharp_arith.ml            Sharpening I: arithmetic of the counterpart.
   - Baker/sharp_sec4.ml             Sharpening I: section 4 of the core (the Kummer step over the field of the alphas and the ...
   - Baker/sharp_core.ml             Sharpening I: the extrapolation and the parametric core.
   - Baker/sharp_num.ml              Sharpening I: the numeric layer.
   - Baker/sharp_tools.ml            Sharpening I: number field tools.
   - Baker/sharp_uniform.ml          Sharpening I: uniform lower bounds for logarithms of bounded size with algebraic coefficients (the ...
   - Baker/sharp_descent.ml          Sharpening I: the tools of both descents and the descent for integer coefficients (Baker, A ...
   - Baker/sharp_main.ml             Sharpening I: the headline forms.

7. Sharpening I with algebraic coefficients (Baker, A central theorem in transcendence theory, 1973; Transcendental Number Theory, p. 23), uniform in the data: the ending for algebraic coefficients of the machinery of section 6. BAKER_SHARPENING_ALGEBRAIC_COEFFS (non-zero algebraic numbers of degree at most d, the first n - 1 of height at most exp g0, the last of height at most A, principal logarithms, algebraic coefficients of degree at most d and height at most B: Lambda = 0 or |Lambda| >= exp(-C g0^K log A log(B log A)), C and K depending only on n and d), SHARPC_SHARPENING_REAL, SHARPC_BAKER; the numeric ending for algebraic coefficients (SHARPC_CORE: the bound functions of the factorial Delta representation are dominated by those of the integer one at the analytic size Bp = (2 Lm + S0) (1 + D)^n B^(3n), the source of log(B log A)) and the normalised descent (bb n = 1) in the fixed field Q(alphas, betas). Needs ANT/ and sections 1 to 6.
   - Baker/sharpc_num.ml             Sharpening I with algebraic coefficients: the numeric layer.
   - Baker/sharpc_descent.ml         Sharpening I with algebraic coefficients: the descent and the bound property (Baker, A central ...
   - Baker/sharpc_main.ml            Sharpening I with algebraic coefficients: the headline forms.

8. Tijdeman (1976) and the Catalan exponents: SHARP_BAKER_RATIONAL and TIJDEMAN_LINEAR_FORMS_RATIONAL (the rational case of Sharpening I: BAKER_SHARPENING_REAL with d = 1), CATALAN_EXPONENT_BOUND. Needs ANT/ and sections 1 to 6.
   - Baker/catalan_nt.ml             Elementary number theory for the Catalan equation x^p - y^q = 1.
   - Baker/catalan.ml                Tijdeman: the Catalan exponents are bounded (conditional form).
   - Baker/tijdeman.ml               Tijdeman Theorem 2 for rationals and the Catalan exponent bound.

9. Two logarithms: an explicit lower bound for linear forms in two logarithms (interpolation determinants; the determinants are ring_det of Library/ring_det.ml over complex_ring and real_ring, COMPLEX_RING_DET, REAL_RING_DET), and the Steiner theorem on the circuits of the 3x+1 problem. Needs only section 1 (Baker/make_twolog.ml).
   - Baker/twolog_det.ml             Two logarithms: determinants of n x n arrays indexed by 1..n.
   - Baker/twolog_interp.ml          Two logarithms: the analytic interpolation lemma for interpolation determinants (Laurent).
   - Baker/twolog_zero.ml            Two logarithms: the zero lemma for C x C-star and the maximal rank of the interpolation matrix.
   - Baker/twolog_core.ml            Two logarithms: the interpolation determinant argument.
   - Baker/twolog_param.ml           Two logarithms: the numeric parameter choice.
   - Baker/twolog.ml                 Two logarithms: the explicit lower bound for linear forms in two logarithms of positive rationals, ...
   - Baker/steiner.ml                The theorem of Steiner (1977) on circuits of the 3x+1 problem.

10. The Laurent bound for two logarithms of rationals (Laurent 2008 at mu = 1): LAURENT_RATIONAL, LAURENT_RATIONAL_GENERAL, LAURENT_RATIONAL_PARAM. Needs only sections 1 and 9 (Baker/make_laurent.ml).
   - Baker/laurent_defs.ml           Two logarithms, the Laurent bound: the definitions of the numeric layer.
   - Baker/laurent_det.ml            Two logarithms, the Laurent bound: determinant tools.
   - Baker/laurent_binom.ml          Two logarithms, the Laurent bound: binomial coefficients as shifted polynomials, and the zero lemma ...
   - Baker/laurent_glemma.ml         Two logarithms, the Laurent bound: the g-lemma.
   - Baker/laurent_interp.ml         Two logarithms, the Laurent bound: the analytic upper bound for the binomial interpolation ...
   - Baker/laurent_core.ml           Two logarithms, the Laurent bound: the arithmetic lower bound and the core for rationals (D = 1, mu ...
   - Baker/laurent_param_main.ml     Two logarithms, the Laurent bound: the parameter recipe of the numeric layer.
   - Baker/laurent_param.ml          Two logarithms, the Laurent bound: the numeric layer.
   - Baker/laurent_corner.ml         Two logarithms, the Laurent bound: the corner constant of Corollary 2.
   - Baker/laurent.ml                Two logarithms, the Laurent bound: the lower bounds for linear forms in two logarithms of rationals.

11. Number fields as conjugate vectors and their orders, the bridge between ANT/ and the conjugate-vector number fields (nf_data gives a number field of degree n with the n embeddings nf_embedding; nf_elem, nf_alg_int, nf_order and nf_unit are the conjugate vectors of K, O_K, Z[r 1] and its units; the product and the sum of the conjugates are the norm and the trace; the Northcott finiteness of the order from that of O_K), units, Thue equations, cubic forms, Mordell equations (the algebraic integers are in section 5). The bridge Baker/ant_bridge_nf.ml and the definitions Baker/laurent_nf_defs.ml of the Laurent bound for algebraic numbers load here, after Baker/nf_order.ml. Needs ANT/ and sections 1 to 6 (Baker/nf_box.ml uses RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED of Baker/sharp_tools.ml).
   - Baker/nf_defs.ml                Number fields as conjugate vectors: the definitions.
   - Baker/nf_order.ml               Number field data and the order Z[theta].
   - Baker/laurent_nf_defs.ml        Two logarithms, the Laurent bound for algebraic numbers: elements, algebraic integers and ...
   - Baker/ant_bridge_nf.ml          The conjugate-vector number fields as number fields of ANT/.
   - Baker/nf_box.ml                 Box principle and elements of bounded norm in the order Z[theta].
   - Baker/nf_units.ml               Units of the order Z[theta].
   - Baker/thue.ml                   The Thue theorem via BAKER_FELDMAN (Baker, Transcendental Number Theory, Ch. 4; Thue 1909).
   - Baker/cubic_reduction.ml        Reduction theory of binary cubic forms (Hermite reduction).
   - Baker/mordell.ml                The Mordell curves y^2 = x^3 + k (Mordell 1922; Baker, Transcendental Number Theory, Ch. 4).

12. Lebesgue and Ko Chao, the S-unit descent in a number field inside C (Baker/schinzel_sunit.ml, with the descent for one root used by section 20), the descent, primitive elements, the unit equation, superelliptic equations, Catalan finiteness. LEBESGUE uses the Gaussian integers as the Euclidean ring imag_quadratic_integers 1 (the imaginary quadratic base files of section 5). Needs ANT/ and sections 1 to 6, 8 and 11.
   - Baker/lebesgue.ml               Gaussian integers and the theorem of Lebesgue (1850).
   - Baker/kochao.ml                 The exponent bound for X^2 = Y^q + 1 (the Ko Chao case of the Catalan reduction; Tijdeman 1976).
   - Baker/schinzel_sunit.ml         The S-unit descent in a number field inside C, for one root of c0 y^m = g(x)^k H(x) (for the ...
   - Baker/descent.ml                The descent for y^m = g(x) w, by the S-unit descent with ANT/.
   - Baker/nf_fields.ml              Primitive elements in the conjugate-vector framework.
   - Baker/uniteq.ml                 The unit equation a u + b v = e in a fixed order.
   - Baker/superell_descent.ml       The superelliptic descent at one simple root.
   - Baker/superell_roots.ml         The superelliptic equation: two simple roots give finitely many x.
   - Baker/superell.ml               The superelliptic theorem (Baker 1969, qualitative form; Baker, Transcendental Number Theory, Ch. ...
   - Baker/catalan_finite.ml         Catalan finiteness (Tijdeman 1976).

13. The Laurent bound for algebraic numbers via pair heights:
    LAURENT_NF_REAL, LAURENT_NF_REAL_PARAM (the definitions
    Baker/laurent_nf_defs.ml are in section 11).
    Needs ANT/ and sections 1, 2, 5 and 9 to 11.
   - Baker/laurent_nf.ml             Two logarithms, the Laurent bound for algebraic numbers: number field infrastructure for heights.
   - Baker/laurent_alg.ml            Two logarithms, the Laurent bound for algebraic numbers: real numbers a_i = be_i / ga_i of a number ...

14. Tools for the Schinzel-Tijdeman theorem, from the proof of its reducible case (whose theorems SCHINZEL_TIJDEMAN_REDUCIBLE, SCHINZEL_TIJDEMAN_FINITE_REDUCIBLE, SCHINZEL_TIJDEMAN_REDUCIBLE_MULT are corollaries in section 20): the bounded power descent over Z (INT_POWER_DESCENT_BOUNDED), logarithms of monic polynomials, exponent bounds, the monic scaling, the multiplicity split and the root data of integer polynomials, used by sections 19 and 20. Needs ANT/ and sections 1 to 6, 11 and 12.
   - Baker/schinzel_descent.ml       The bounded power descent over Z (for the Schinzel-Tijdeman theorem).
   - Baker/schinzel_poly.ml          Tools for the Schinzel-Tijdeman theorem: the logarithm of a monic polynomial.
   - Baker/schinzel.ml               Tools for the Schinzel-Tijdeman theorem: exponent bounds and integer polynomials.
   - Baker/schinzel_mult.ml          Tools for the Schinzel-Tijdeman theorem: the multiplicity split and the root data of an integer ...

15. The class number one problem (Baker 1966 / Gauss): imaginary quadratic fields of class number one: CLASS_NUMBER_ONE (exactly the nine d = 1, 2, 3, 7, 11, 19, 43, 67, 163), CLASS_NUMBER_ONE_BOUND_LAURENT (d < 10^16 by the Laurent bound), CLASS_NUMBER_ONE_FINITE. With the general machinery of binary quadratic forms shared with section 22: reduction, the evaluator of form_classno (QF_FORMS_EVAL, FORM_CLASSNO_CONV), representation numbers, the lattice series of a positive definite form twisted by a real character and the limit formula at s = 1 (Baker/qform_limit.ml, Baker/qform_series.ml), from which the identity for the principal form follows (Baker/classno_product.ml). Needs Library/jacobi.ml, 100/dirichlet.ml and Multivariate/gamma.ml (Jacobi symbols, Dirichlet L-functions, the sine product); ANT/ and sections 1 to 6, 9 to 11 and 13 (with the definitions Baker/classno_defs.ml at the end of section 5, and Baker/kummer.ml of section 6 for CLASSNO_NF_SQRT_INDEPENDENT).
   - Baker/classno_forms.ml          Reduced binary quadratic forms: reduction, the evaluator of the class number, witnesses, the nine ...
   - Baker/classno_chardefs.ml       The class number one problem: real characters and the lattice sums of a binary quadratic form ...
   - Baker/classno_rep.ml            Representation numbers of positive definite binary quadratic forms; the representation numbers of ...
   - Baker/classno_series_lib.ml     Series tools: interlacing of unimodal sums, Dirichlet products, right continuity of L-series.
   - Baker/classno_series.ml         The real quadratic characters as Dirichlet characters, and series tools for the lattice series of ...
   - Baker/classno_poisson.ml        The Poisson kernel identity: the sum over all integers n of 1 / ((n + t)^2 + c^2).
   - Baker/classno_limit.ml          The limit formula at s = 1: the Poisson kernel up to an exponentially small error, and the mean of ...
   - Baker/classno_gauss.ml          Gauss sums of real characters and the class number formulas of Dirichlet in absolute value.
   - Baker/qform_limit.ml            The limit formula at s = 1 for a general positive definite binary quadratic form and a general ...
   - Baker/qform_series.ml           The lattice series of a positive definite binary quadratic form twisted by a real character: the ...
   - Baker/classno_product.ml        The class number one problem: the product of two L-series at s = 1 as the lattice series of the ...
   - Baker/classno_cyclo.ml          The values of L(1, chi) for k = 21 and k = 33 as finite cyclotomic identities.
   - Baker/classno_nf.ml             The field Q(sqrt 21, sqrt 33) and the Laurent bound for the logarithms of its units.
   - Baker/classno_cf.ml             Enclosures of log eps_21 and log eps_33 and the two continued-fraction stages of the endgame.
   - Baker/classno_linear.ml         The linear form in log eps_21 and log eps_33 attached to an imaginary quadratic field of class ...
   - Baker/classno_main.ml           The class number one problem: the imaginary quadratic fields of class number one.

16. Unique factorization in imaginary quadratic fields: the field Q(sqrt(-d)) as a number field of ANT/ (the field, its discriminant qdisc d and its ring of integers Z[omega] are the imaginary quadratic base files at the end of section 5): the ring of integers is a UFD, equivalently a PID, equivalently of class number one, iff d = m^2 k with k in the nine of Gauss: CLASS_NUMBER_ONE_UFD, CLASS_NUMBER_ONE_PID, CLASS_NUMBER_ONE_IDEAL_CLASSES, CLASS_NUMBER_ONE_UNIQUE_FACTORIZATION; for every number field of degree 2 with negative discriminant d_k: class number one iff d_k is one of the nine discriminants (IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE). Needs ANT/ and sections 1 to 6, 9 to 11, 13 and 15 (section 5: number fields inside C, rings of integers are algebraic integers, the prime subfield is Q; the imaginary quadratic base files).
   - Baker/quadint_ufd.ml            Unique factorization in the ring of integers of Q(sqrt(-d)) forces class number one.
   - Baker/quadint_pid.ml            Class number one gives a principal ideal domain (the form/ideal dictionary for h = 1).
   - Baker/quadint_main.ml           The ring of integers of Q(sqrt(-d)) is a UFD, equivalently a PID, equivalently of class number one, ...
   - Baker/quadint_intrinsic.ml      The class number one theorem for an abstract imaginary quadratic field.

17. Diophantine applications of unique factorization in imaginary quadratic fields: RAMANUJAN_NAGELL (x^2 + 7 = 2^n), FERMAT_SQUARE_CUBE and FERMAT_26 (x^2 + 2 = y^3), FLT3 (Fermat Last Theorem for the exponent 3). Needs only ANT/ufd.ml and the imaginary quadratic base files at the end of section 5 (unique factorization from the Euclidean algorithm, IMAG_QUADRATIC_INTEGERS_UFD): sections 1, 2 and 5.
   - Baker/ramanujan_nagell.ml       The Ramanujan-Nagell theorem: x^2 + 7 = 2^n only for (x, n) = (1, 3), (3, 4), (5, 5), (11, 7), ...
   - Baker/fermat26.ml               Fermat: the only integer solutions of x^2 + 2 = y^3 are x = +-5, y = 3; so 26 is the only natural ...
   - Baker/flt3.ml                   Fermat Last Theorem for the exponent 3 (Euler), by descent in the ring of Eisenstein integers.

18. The hyperelliptic equation (Baker 1969) and integral points on elliptic curves (Baker 1968): HYPERELLIPTIC, SUPERELLIPTIC_SIMPLE_ROOTS (all m >= 2), ELLIPTIC_INTEGRAL_POINTS, ELLIPTIC_CUBIC_INTEGRAL_POINTS, WEIERSTRASS_INTEGRAL_POINTS. Needs ANT/ and sections 1 to 6, 11 and 12.
   - Baker/hyperell_roots.ml         The hyperelliptic equation: three simple roots give finitely many x.
   - Baker/hyperell.ml               The hyperelliptic theorem (Baker 1969, qualitative form; Siegel 1926) and the superelliptic theorem ...
   - Baker/elliptic.ml               Integral points on elliptic curves (Baker 1968, the elliptic equation; Siegel 1929 for genus 1 in ...

19. The prime factors of the values of an integer polynomial with two distinct roots, a classical theorem (Polya, Siegel): POLY_SMOOTH_VALUES_FINITE (only finitely many x with f(x) <> 0 and all prime factors in a finite set S), POLY_LARGEST_PRIME_FACTOR (the greatest prime factor of f(x) tends to infinity), POLY_SMOOTH_VALUES_FINITE_SIMPLE, POLY_PRIME_POWER_VALUES_FINITE and the corollaries for x^2 + D; through SUPERELLIPTIC (m = 3). Needs ANT/ and sections 1 to 6, 11, 12 and 14.
   - Baker/prime_factors.ml          Prime factors of the values of an integer polynomial: the greatest prime factor of f(x) tends to ...

20. The Schinzel-Tijdeman theorem (Acta Arith. 31, 1976): SCHINZEL_TIJDEMAN (f with integer coefficients and two distinct complex roots, of any multiplicities: the integer solutions of y^m = f(x) with |y| >= 2 have bounded m), SCHINZEL_TIJDEMAN_FINITE (two simple roots: finitely many solutions with m >= 3), SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS, SQUARE_PLUS_POW_FINITE (x^2 + D = y^n with D <> 0); per root the S-unit descent with ANT/ (SCHINZEL_TIJDEMAN_ROOT_DESCENT of Baker/schinzel_sunit.ml, section 12), then one linear form in logarithms for any two distinct roots, bounded below by SHARP_BAKER_NUMBER_FIELD; the reducible case (SCHINZEL_TIJDEMAN_REDUCIBLE, SCHINZEL_TIJDEMAN_FINITE_REDUCIBLE, SCHINZEL_TIJDEMAN_REDUCIBLE_MULT) as corollaries. Needs ANT/ and sections 1 to 6, 11, 12, 14, 18 and 19.
   - Baker/schinzel_general.ml       The Schinzel-Tijdeman theorem for every integer polynomial with two distinct complex roots, and its ...

21. Perfect powers in Lucas sequences and the equations x^k + D = y^n, applications of the Schinzel-Tijdeman theorem: LUCAS_PERFECT_POWERS_FINITE (u_0 = 0, u_1 = 1, u_(n+2) = P u_(n+1) - Q u_n with Q = 1 or Q = -1 and P^2 <> 4 Q: only finitely many perfect powers y^m with |y| >= 2, m >= 2), LUCAS_COMPANION_PERFECT_POWERS_FINITE (v_0 = 2, v_1 = P, every P), FIBONACCI_PERFECT_POWERS_FINITE (fib of Examples/gcdrecurrence.ml), PELL_PERFECT_POWERS_FINITE, LUCAS_NUMBERS_PERFECT_POWERS_FINITE, POW_PLUS_POW_FINITE (x^k + D = y^n for fixed k >= 2 and D <> 0), SQUARE_PLUS_MUL_POW_FINITE (x^2 + C = D y^n, n >= 3). Needs ANT/ and sections 1 to 6, 11, 12, 14 and 18 to 20 (SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA is in section 19) and Examples/gcdrecurrence.ml.
   - Baker/perfect_powers.ml         Perfect powers in Lucas sequences and the equations x^k + D = y^n: applications of the ...

22. Imaginary quadratic fields of class number two (Baker 1971, Stark 1971; Baker, Transcendental Number Theory, Ch. 5, sec. 5): CLASS_NUMBER_TWO_FINITE (only finitely many squarefree d with form_classno (qdisc d) = 2), CLASS_NUMBER_TWO_FINITE_ODD, CLASS_NUMBER_TWO_EXAMPLES (the eighteen known d have class number two); genus theory for class number two by witnesses (CN_FORMS_TWO_CASES, CN_GENUS_CHARACTER), the representation numbers of the two forms of discriminant -d and -4d, the genus and total product identities of L-series at s = 1 (with the general form machinery of section 15), the cyclotomic unit lemma (CN_CYCLO_UNIT_QUADRATIC) and |L(1,chi)| <= log m + 3, the class number formula for the odd characters of even modulus, zeta(2) = pi^2/6, the three linear forms in logarithms (CN_LINEAR_MAIN, CN_LINEAR_SMALL, CN_LINEAR_EVEN), closed by BAKER_SHARPENING_ALGEBRAIC_COEFFS (section 7) and BAKER_FELDMAN. Needs ANT/ and sections 1 to 7, 9 to 11, 13 and 15.
   - Baker/cn_defs.ml                Class number two: the definitions.
   - Baker/cn_forms.ml               Class number two: the cases of the discriminant, the genus character and the eighteen known ...
   - Baker/cn_rep.ml                 The representation numbers of the two forms of discriminant -d, d = p q, when the class number is ...
   - Baker/cn_cyclo.ml               The cyclotomic unit of a real quadratic field of composite discriminant, and an explicit bound for ...
   - Baker/cn_gauss_even.ml          The class number formula in absolute value for the odd characters of even modulus, chi = (-4 k d / ...
   - Baker/cn_rep_even.ml            The representation numbers of the two forms of discriminant -4 d when the class number is two.
   - Baker/cn_zeta.ml                zeta(2) = pi^2 / 6.
   - Baker/cn_products.ml            Products of two L-series at s = 1 as lattice sums: the genus identity and the total identities of ...
   - Baker/cn_linear.ml              The three linear forms in logarithms of the class number two problem.
   - Baker/cn_main.ml                Class number two: only finitely many imaginary quadratic fields have class number two (Baker 1971, ...

## References

A. Baker, Transcendental Number Theory (CUP 1975); A. Baker, A sharpening of
the bounds for linear forms in logarithms I-III, Acta Arith. 21 (1972), 24
(1973), 27 (1975); A. Baker, G. Wustholz, Logarithmic Forms and Diophantine
Geometry (CUP 2007); R. Tijdeman, On the equation of Catalan, Acta Arith. 29
(1976); A. Schinzel, R. Tijdeman, On the equation y^m = P(x), Acta Arith. 31
(1976); Y. Bugeaud, Linear Forms in Logarithms and Applications (EMS 2018);
M. Laurent, Linear forms in two logarithms and interpolation determinants,
Acta Arith. 66 (1994), II, Acta Arith. 133 (2008); M. Laurent, M. Mignotte,
Yu. Nesterenko, J. Number Theory 55 (1995); D. Lombardo, Interpolation
determinants and the Lebesgue-Nagell equation (arXiv 2609.23899, 2026);
R. P. Steiner, A theorem on the Syracuse problem (1977); C. F. Gauss,
Disquisitiones Arithmeticae (1801), art. 303; K. Heegner, Diophantische
Analysis und Modulfunktionen, Math. Z. 56 (1952); A. Baker, Linear forms in
the logarithms of algebraic numbers I, Mathematika 13 (1966); H. M. Stark, A
complete determination of the complex quadratic fields of class-number one,
Michigan Math. J. 14 (1967); A. O. Gelfond, Yu. V. Linnik, Doklady Akad.
Nauk SSSR 61 (1948); A. Baker, H. Davenport, The equations 3x^2 - 2 = y^2
and 8x^2 - 7 = z^2, Quart. J. Math. Oxford 20 (1969); E. Landau, Vorlesungen
ueber Zahlentheorie (1927), Satz 204.
