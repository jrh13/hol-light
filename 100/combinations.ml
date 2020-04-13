(* ========================================================================= *)
(* Binomial coefficients and relation to number of combinations.             *)
(* ========================================================================= *)

needs "Library/binomial.ml";;

(* ------------------------------------------------------------------------- *)
(* The theorem is really proved in that library file; reformulate it a bit.  *)
(* ------------------------------------------------------------------------- *)

let NUMBER_OF_COMBINATIONS = prove
 (`!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE binom(n,m)`,
  MATCH_ACCEPT_TAC HAS_SIZE_RESTRICTED_POWERSET);;

let NUMBER_OF_COMBINATIONS_EXPLICIT = prove
 (`!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE
            (if n < m then 0 else FACT(n) DIV (FACT(m) * FACT(n - m)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `m:num` o MATCH_MP NUMBER_OF_COMBINATIONS) THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP; BINOM; MULT_AC]);;
