(* ========================================================================= *)
(* Elliptic curves of various forms and specific ones for cryptography.      *)
(* ========================================================================= *)

needs "Library/pocklington.ml";;
needs "Library/primitive.ml";;
needs "Library/grouptheory.ml";;
needs "Library/ringtheory.ml";;

(* ------------------------------------------------------------------------- *)
(* A few extras to support all the curve proofs.                             *)
(* ------------------------------------------------------------------------- *)

loadt "EC/misc.ml";;

(* ------------------------------------------------------------------------- *)
(* Short Weierstrass, Montgomery and Edwards curves (independently).         *)
(* ------------------------------------------------------------------------- *)

loadt "EC/weierstrass.ml";;
loadt "EC/montgomery.ml";;
loadt "EC/edwards.ml";;

(* ------------------------------------------------------------------------- *)
(* Projective, Jacobian and projective-without-y coordinates.                *)
(* ------------------------------------------------------------------------- *)

loadt "EC/projective.ml";;
loadt "EC/jacobian.ml";;
loadt "EC/xzprojective.ml";;

(* ------------------------------------------------------------------------- *)
(* Some traditional formulas for evaluation in these coordinate systems.     *)
(* ------------------------------------------------------------------------- *)

loadt "EC/formulary_projective.ml";;
loadt "EC/formulary_jacobian.ml";;
loadt "EC/formulary_xzprojective.ml";;

(* ------------------------------------------------------------------------- *)
(* Translations between curves: Edwards <-> Montgomery <-> Weierstrass.      *)
(* ------------------------------------------------------------------------- *)

loadt "EC/edmont.ml";;
loadt "EC/montwe.ml";;

(* ------------------------------------------------------------------------- *)
(* Additional computational derived rules.                                   *)
(* ------------------------------------------------------------------------- *)

loadt "EC/excluderoots.ml";;
loadt "EC/computegroup.ml";;

(* ------------------------------------------------------------------------- *)
(* The NIST curves over prime characteristic fields.                         *)
(* ------------------------------------------------------------------------- *)

loadt "EC/nistp192.ml";;
loadt "EC/nistp224.ml";;
loadt "EC/nistp256.ml";;
loadt "EC/nistp384.ml";;
loadt "EC/nistp521.ml";;

(* ------------------------------------------------------------------------- *)
(* The (other) SECG curves over prime characteristic fields                  *)
(* ------------------------------------------------------------------------- *)

loadt "EC/secp192k1.ml";;
loadt "EC/secp224k1.ml";;
loadt "EC/secp256k1.ml";;

(* ------------------------------------------------------------------------- *)
(* The curve25519 family in Edwards, Montgomery and Weierstrass forms.       *)
(* The first three files are independent, the fourth giving the connections. *)
(* ------------------------------------------------------------------------- *)

loadt "EC/edwards25519.ml";;
loadt "EC/curve25519.ml";;
loadt "EC/wei25519.ml";;
loadt "EC/family25519.ml";;
