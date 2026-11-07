(* ========================================================================= *)
(* Sharpening I (Baker 1972, 1973): the definitions of the machinery.        *)
(*                                                                           *)
(* Purpose: the definitions of Baker/make.ml section 6, one machinery for    *)
(* linear forms Lambda = bb 1 lg 1 + ... + bb n lg n in principal logarithms *)
(* of algebraic numbers cexp(lg r) with integer or algebraic coefficients bb *)
(* r (Baker, A sharpening of the bounds for linear forms in logarithms I,    *)
(* Acta Arith. 21 (1972); A central theorem in transcendence theory, 1973),  *)
(* and the core and bound properties of its two endings.                     *)
(*                                                                           *)
(*  - sharp_index: the index set of the auxiliary polynomial.                *)
(*  - sharp_x, sharp_omega, sharp_term, sharp_aux, sharp_algterm,            *)
(*    sharp_alg, sharp_coeff, sharp_coeff0: the auxiliary function of        *)
(*    Sharpening I with complex coefficients bb r (integer coefficients b r  *)
(*    are the case bb r = Cx(b r)).                                          *)
(*  - sharp_algdata: classical height data of the numbers cexp(lg r).        *)
(*  - sharp_deltarep: an integer polynomial representation of the Delta      *)
(*    factors prod_r Delta(x_r; m_r) in the 2n numbers (alphas, bb r): the   *)
(*    integer values of the Baker binomial trick for integer coefficients    *)
(*    (multiplier 1), the polynomials prod_j (x_r + j) with the factorial    *)
(*    multiplier prod_r m_r! for algebraic coefficients.                     *)
(*  - sharp_psize, sharp_liou5, sharp_lb8: the Siegel bound and the          *)
(*    Liouville lower bounds of the counterpart at l and at l/q, for any     *)
(*    Delta representation (sizes W, degrees E, multiplier bound Mb) and     *)
(*    coefficient data (degrees db, height Hb).                              *)
(*  - sharp_ubd, sharp_errb, sharp_lv: the size functions of the             *)
(*    parametric core and the parameter map.                                 *)
(*  - sharp_nfbound: an element of a subfield of C with an integer           *)
(*    denominator and bounded conjugates (the descents).                     *)
(*  - sharp_core_property_alg, sharp_bound_property_alg: the ending for      *)
(*    integer coefficients (bound exp(-C g0^K log A log B)).                 *)
(*  - sharpc_core_property, sharpc_bound_property: the ending for algebraic  *)
(*    coefficients (bound exp(-C g0^K log A log(B log A))), with the         *)
(*    coefficient data sharpc_coefdata of Baker/uniform.ml.                  *)
(*                                                                           *)
(* Uses: Baker/delta.ml (feldman_delta, feldman_basis), Baker/intpoly.ml     *)
(* (intpoly), Baker/uniform.ml (sharpc_coefdata), Baker/algint.ml            *)
(* (algebraic_integer), ANT/complex_embeddings.ml (complex_embeddings),      *)
(* Library/fieldtheory.ml (subfield_generated), Multivariate/complex_ring.ml *)
(* (complex_ring), Multivariate/canal.ml (higher_complex_derivative, loaded  *)
(* with Multivariate/cauchy.ml).                                             *)
(* ========================================================================= *)

needs "ANT/complex_embeddings.ml";;
needs "Baker/uniform.ml";;
needs "Baker/algint.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The index set of the auxiliary polynomial: lambda = (a,b,mu) with a < h,  *)
(* b <= L0 and mu r <= Lv r (r = 1..n).                                      *)
(* ------------------------------------------------------------------------- *)

let sharp_index = new_definition
 `sharp_index h L0 (Lv:num->num) n =
    {a:num | a < h} CROSS
    ((0..L0) CROSS cartesian_product (1..n) (\r. 0..Lv r))`;;

(* ------------------------------------------------------------------------- *)
(* The auxiliary function with complex coefficients bb r (r = 1..n): the     *)
(* nodes x_r = bb n mu_r - bb r mu_n, omega, the terms, the auxiliary        *)
(* function, its counterpart with cexp(z sum_r mu_r lg r) and the            *)
(* coefficients of the derivative relation. For integer coefficients b r     *)
(* take bb r = Cx(b r).                                                      *)
(* ------------------------------------------------------------------------- *)

let sharp_x = new_definition
 `sharp_x n (bb:num->complex) (mu:num->num) r =
    bb n * Cx(&(mu r)) - bb r * Cx(&(mu n))`;;

let sharp_omega = new_definition
 `sharp_omega n (bb:num->complex) (lg:num->complex) (mu:num->num) =
    vsum(1..n-1) (\r. (sharp_x n bb mu r / bb n) * lg r)`;;

let sharp_term = new_definition
 `sharp_term n h (p:num#num#(num->num)->real) (bb:num->complex)
             (lg:num->complex) (m:num->num) (a,b,mu) z =
    Cx(p(a,b,mu)) *
    (higher_complex_derivative (m 0) (feldman_basis h a b) z /
     Cx(&(FACT(m 0)))) *
    cproduct(1..n-1) (\r. feldman_delta (m r) (sharp_x n bb mu r)) *
    cexp(z * sharp_omega n bb lg mu)`;;

let sharp_aux = new_definition
 `sharp_aux n h L0 Lv p bb lg m z =
    vsum (sharp_index h L0 Lv n) (\x. sharp_term n h p bb lg m x z)`;;

let sharp_algterm = new_definition
 `sharp_algterm n h (p:num#num#(num->num)->real) (bb:num->complex)
                (lg:num->complex) (m:num->num) (a,b,mu) z =
    Cx(p(a,b,mu)) *
    (higher_complex_derivative (m 0) (feldman_basis h a b) z /
     Cx(&(FACT(m 0)))) *
    cproduct(1..n-1) (\r. feldman_delta (m r) (sharp_x n bb mu r)) *
    cexp(z * vsum(1..n) (\r. Cx(&(mu r)) * lg r))`;;

let sharp_alg = new_definition
 `sharp_alg n h L0 Lv p bb lg m z =
    vsum (sharp_index h L0 Lv n) (\x. sharp_algterm n h p bb lg m x z)`;;

let sharp_coeff = new_definition
 `sharp_coeff n (bb:num->complex) (lg:num->complex) (m:num->num) i =
    if i = 0 then Cx(&(m 0 + 1)) else Cx(&(m i + 1)) * lg i / bb n`;;

let sharp_coeff0 = new_definition
 `sharp_coeff0 n (bb:num->complex) (lg:num->complex) (m:num->num) =
    --vsum(1..n-1) (\i. Cx(&(m i + 1)) * lg i / bb n)`;;

(* ------------------------------------------------------------------------- *)
(* Classical height data of the logarithms lg r (r = 1..n).                  *)
(* ------------------------------------------------------------------------- *)

let sharp_algdata = new_definition
 `sharp_algdata n (lg:num->complex) (a:num->num->real) (dd:num->num)
                (H:num->real) <=>
    !r. r IN 1..n
        ==> 1 <= dd r /\ &1 <= H r /\
            (!j. integer(a r j) /\ abs(a r j) <= H r) /\
            ~(a r (dd r) = &0) /\
            vsum(0..dd r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* The Delta representation (W, E, Mb, M): for every vector m of derivative  *)
(* orders, M m times the Delta product of every index mu with mu r <= Lm     *)
(* is an integer polynomial over the 2n numbers (k <= n: the alphas,         *)
(* k = n + r: the coefficients bb r) of degree 0 in the alphas and           *)
(* E s in the coefficients, with coefficient sum at most W s, where          *)
(* s = m 1 + ... + m (n-1); 1 <= M m <= Mb s; W, E, Mb monotone.             *)
(* Integer coefficients: M = 1, E = 0, W s = (4B+2)^s 2^((n-1)Lm) (the       *)
(* Delta values are integers); algebraic coefficients: M m = prod m_r!,      *)
(* E s = s, W s = (2Lm+s)^s, Mb s = s^s (m! Delta(x;m) is a polynomial).     *)
(* ------------------------------------------------------------------------- *)

let sharp_deltarep = new_definition
 `sharp_deltarep n (bb:num->complex) Lm (W:num->real) (E:num->num)
                 (Mb:num->real) (M:(num->num)->num) <=>
    (!s t. s <= t ==> W s <= W t /\ E s <= E t /\ Mb s <= Mb t) /\
    (!m. 1 <= M m /\ &(M m) <= Mb(nsum(1..n-1) m) /\
         !mu. (!r. r IN 1..n ==> mu r <= Lm)
              ==> ?g. intpoly (1..n+n)
                        (\k. if k <= n then 0 else E(nsum(1..n-1) m))
                        (W(nsum(1..n-1) m)) g /\
                      (!x. (!r. r IN 1..n ==> x(n + r) = bb r)
                           ==> g x = Cx(&(M m)) *
                                     cproduct(1..n-1)
                                      (\r. feldman_delta (m r)
                                             (sharp_x n bb mu r))))`;;

(* ------------------------------------------------------------------------- *)
(* The Siegel bound and the Liouville lower bounds at an integer point l     *)
(* and at a rational point l/q for the counterpart, for any Delta            *)
(* representation (W, E, Mb) and coefficient data (db, Hb): the forms of     *)
(* ALGEBRAIC_SIEGEL and INTPOLY_LIOUVILLE over the 2n numbers.               *)
(* ------------------------------------------------------------------------- *)

let sharp_psize = new_definition
 `sharp_psize n h L0 Lv S0 (H:num->real) (Hb:real) (W:num->real)
              (E:num->num) =
    &(CARD(sharp_index h L0 Lv n)) *
    max (&1)
        (exp(&36 * &h * &S0) * &2 pow ((L0 + 2) * (2 * h + 1)) * W S0 *
         product(1..n) (\r. (&2 * H r) pow (Lv r * h)) *
         (&2 * Hb) pow (n * E S0))`;;

let sharp_liou5 = new_definition
 `sharp_liou5 n h L0 Lv P S0 (dd:num->num) (H:num->real) (db:num->num)
              (Hb:real) (W:num->real) (E:num->num) (Mb:num->real) l =
    inv((exp(&19) * (&l + &h) / &h) pow (h * S0) * Mb S0 *
        &(FACT(nproduct(1..n) dd * nproduct(1..n) db)) *
        (max (&1)
          ((&(CARD(sharp_index h L0 Lv n)) * P *
            (exp(&19) * (&l + &h) / &h) pow (h * S0) *
            &2 pow ((L0 + 2) * ((l + 1) + h)) * W S0) *
           product(1..n) (\r. H r pow (Lv r * l)) * Hb pow (n * E S0) *
           product(1..n) (\r. (H r * (&1 + &(dd r) * H r)) pow (Lv r * l)) *
           product(1..n) (\r. (Hb * (&1 + &(db r) * Hb)) pow (E S0))))
        pow (nproduct(1..n) dd * nproduct(1..n) db - 1) *
        product(1..n) (\r. H r pow (Lv r * l)) * Hb pow (n * E S0))`;;

let sharp_lb8 = new_definition
 `sharp_lb8 n h L0 Lv P (dd:num->num) (H:num->real) (db:num->num)
            (Hb:real) (W:num->real) (E:num->num) (Mb:num->real)
            (m:num->num) l q Nz =
    inv(&(FACT(nproduct(1..n) (\r. q * dd r) * nproduct(1..n) db)) *
        (max (&1)
          ((&(CARD(sharp_index h L0 Lv n)) * P *
            (&q pow (2 * h * (L0 + 2)) * exp(&18 * &(l + q * h)) pow (m 0)) *
            &2 pow ((L0 + 2) * (Nz + h)) * W (nsum(1..n-1) m)) *
           product(1..n) (\r. H r pow (Lv r * l)) *
           Hb pow (n * E (nsum(1..n-1) m)) *
           product(1..n) (\r. (H r * (&1 + &(q * dd r) * H r))
                              pow (Lv r * l)) *
           product(1..n) (\r. (Hb * (&1 + &(db r) * Hb))
                              pow (E (nsum(1..n-1) m)))))
        pow (nproduct(1..n) (\r. q * dd r) * nproduct(1..n) db - 1) *
        product(1..n) (\r. H r pow (Lv r * l)) *
        Hb pow (n * E (nsum(1..n-1) m))) /
    (&q pow (2 * h * (L0 + 2)) * exp(&18 * &(l + q * h)) pow (m 0) *
     Mb (nsum(1..n-1) m))`;;

(* ------------------------------------------------------------------------- *)
(* Size functions of the parametric core: the upper bound sharp_ubd and      *)
(* the approximation error sharp_errb of the auxiliary function (pure real   *)
(* functions of the analytic size bound B), and the parameter map            *)
(* sharp_lv.                                                                 *)
(* ------------------------------------------------------------------------- *)

let sharp_ubd = new_definition
 `sharp_ubd n h L0 Lv Lm P B S0 T0 N z =
    &(CARD(sharp_index h L0 Lv n)) * P * &2 pow ((L0 + 2) * (N + h)) *
    (&4 * B + &2) pow S0 * &2 pow ((n - 1) * Lm) * exp(z * T0)`;;

let sharp_errb = new_definition
 `sharp_errb n h L0 Lv Lm P B S0 T0 d0 N z =
    &(CARD(sharp_index h L0 Lv n)) * P * &2 pow ((L0 + 2) * (N + h)) *
    (&4 * B + &2) pow S0 * &2 pow ((n - 1) * Lm) *
    (z * d0 * exp(z * (T0 + d0)))`;;

let sharp_lv = new_definition
 `sharp_lv n L Ln = \r:num. if r = n then Ln else (L:num)`;;

(* ------------------------------------------------------------------------- *)
(* An element of a subfield of C with an integer denominator and             *)
(* conjugates of modulus at most R.                                          *)
(* ------------------------------------------------------------------------- *)

let sharp_nfbound = new_definition
 `sharp_nfbound s (x:complex) den R <=>
    x IN ring_carrier(subfield_generated complex_ring s) /\
    integer den /\ &1 <= den /\ algebraic_integer(Cx den * x) /\
    (!g. g IN complex_embeddings(subfield_generated complex_ring s)
         ==> norm(g x) <= R)`;;

(* ------------------------------------------------------------------------- *)
(* The ending for integer coefficients: the core property (a tiny linear     *)
(* form forces a Kummer relation for the last number with a large prime)     *)
(* and the bound property (Lambda = 0 or |Lambda| >= exp(-C g0^K log A       *)
(* log B)).                                                                  *)
(* ------------------------------------------------------------------------- *)

let sharp_core_property_alg = new_definition
 `sharp_core_property_alg n D C K cB <=>
    !(lg:num->complex) (a:num->num->real) (dd:num->num) (bb:num->real)
     A B g0.
      &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
      sharp_algdata n lg a dd (\r. if r = n then A else exp g0) /\
      (!r. r IN 1..n
           ==> dd r <= D /\ --pi < Im(lg r) /\ Im(lg r) <= pi /\
               integer(bb r) /\ abs(bb r) <= B) /\
      ~(bb n = &0) /\
      norm(vsum(1..n) (\r. Cx(bb r) * lg r)) <
      exp(--(C * g0 pow K * log A * log B))
      ==> ?pr jj g. prime pr /\ 4 * D EXP 2 <= pr /\
                    &pr <= cB * g0 pow K /\ (!r. jj r < pr) /\
                    g IN ring_carrier(subfield_generated complex_ring
                                       (IMAGE (\r. cexp(lg r)) (1..n))) /\
                    cexp(lg n) =
                    cproduct(1..n-1) (\r. cexp(lg r) pow jj r) * g pow pr`;;

let sharp_bound_property_alg = new_definition
 `sharp_bound_property_alg n d C K <=>
    !(lg:num->complex) (a:num->num->real) (dd:num->num) (bb:num->real)
     A B g0.
      &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
      sharp_algdata n lg a dd (\r. if r = n then A else exp g0) /\
      (!r. r IN 1..n
           ==> dd r <= d /\ --pi < Im(lg r) /\ Im(lg r) <= pi /\
               integer(bb r) /\ abs(bb r) <= B) /\
      ~(vsum(1..n) (\r. Cx(bb r) * lg r) = Cx(&0))
      ==> exp(--(C * g0 pow K * log A * log B)) <=
          norm(vsum(1..n) (\r. Cx(bb r) * lg r))`;;

(* ------------------------------------------------------------------------- *)
(* The ending for algebraic coefficients: the core property (a tiny          *)
(* normalised linear form, bb n = 1, forces a Kummer relation, g in the      *)
(* field of the alphas and the betas) and the bound property (Lambda = 0     *)
(* or |Lambda| >= exp(-C g0^K log A log(B log A))).                          *)
(* ------------------------------------------------------------------------- *)

let sharpc_core_property = new_definition
 `sharpc_core_property n D C K cB <=>
    !(lg:num->complex) (a:num->num->real) (dd:num->num) (bb:num->complex)
     (ab:num->num->real) (db:num->num) A B g0.
      &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
      sharp_algdata n lg a dd (\r. if r = n then A else exp g0) /\
      sharpc_coefdata n bb ab db B /\ bb n = Cx(&1) /\
      (!r. r IN 1..n
           ==> dd r <= D /\ db r <= D /\ --pi < Im(lg r) /\ Im(lg r) <= pi) /\
      norm(vsum(1..n) (\r. bb r * lg r)) <
      exp(--(C * g0 pow K * log A * log(B * log A)))
      ==> ?pr jj g. prime pr /\ 4 * D EXP 2 <= pr /\
                    &pr <= cB * g0 pow K /\ (!r. jj r < pr) /\
                    g IN ring_carrier(subfield_generated complex_ring
                                       (IMAGE (\r. cexp(lg r)) (1..n) UNION
                                        IMAGE bb (1..n))) /\
                    cexp(lg n) =
                    cproduct(1..n-1) (\r. cexp(lg r) pow jj r) * g pow pr`;;

let sharpc_bound_property = new_definition
 `sharpc_bound_property n d C K <=>
    !(lg:num->complex) (a:num->num->real) (dd:num->num) (bb:num->complex)
     (ab:num->num->real) (db:num->num) A B g0.
      &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
      sharp_algdata n lg a dd (\r. if r = n then A else exp g0) /\
      sharpc_coefdata n bb ab db B /\
      (!r. r IN 1..n
           ==> dd r <= d /\ db r <= d /\ --pi < Im(lg r) /\ Im(lg r) <= pi) /\
      ~(vsum(1..n) (\r. bb r * lg r) = Cx(&0))
      ==> exp(--(C * g0 pow K * log A * log(B * log A))) <=
          norm(vsum(1..n) (\r. bb r * lg r))`;;
