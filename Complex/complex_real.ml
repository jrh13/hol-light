(* ========================================================================= *)
(* Trivial restriction of complex Groebner bases to reals.                   *)
(* ========================================================================= *)

let GROBNER_REAL_ARITH =
  let trans_conv = GEN_REWRITE_CONV TOP_SWEEP_CONV
     [GSYM CX_INJ; CX_POW; CX_MUL; CX_ADD; CX_NEG; CX_SUB] in
  fun tm -> let th = trans_conv tm in
            EQ_MP (SYM th) (COMPLEX_ARITH(rand(concl th)));;
