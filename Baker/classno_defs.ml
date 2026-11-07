(* ========================================================================= *)
(* The class number one problem: binary quadratic forms and the class number *)
(* of Gauss (definitions).                                                   *)
(*                                                                           *)
(* Purpose: Gauss (Disquisitiones Arithmeticae, sec. V) divides the positive *)
(* definite binary quadratic forms a x^2 + b x y + c y^2 of discriminant     *)
(* D = b^2 - 4 a c < 0 into classes under unimodular substitutions, and      *)
(* every class contains exactly one reduced form. Here the class number is   *)
(* defined as the number of reduced primitive forms: form_classno D is the   *)
(* number of integer triples (a,b,c) with qf_reduced a b c (0 < a,           *)
(* abs b <= a <= c, and b >= 0 if abs b = a or a = c), b^2 - 4 a c = D and   *)
(* gcd(a, gcd(b, c)) = 1 (it is 0 for D >= 0). qdisc d is the discriminant   *)
(* of Q(sqrt(-d)) for squarefree d (-d if d = 3 mod 4, -4 d otherwise);      *)
(* prin_form d x y = x^2 + x y + ((d + 1) DIV 4) y^2 is the principal form   *)
(* of discriminant -d (d = 3 mod 4), and prin_rep d l the number of its      *)
(* representations of l.                                                     *)
(*                                                                           *)
(* Note: the identification of form_classno (qdisc d) with the class number  *)
(* of the ring of integers of Q(sqrt(-d)) (the dictionary between forms and  *)
(* ideal classes) is formalised for class number one only                    *)
(* (QUAD_UFD_EQ_CLASSNO_ONE and IMAG_QUADRATIC_CLASS_NUMBER_1_EQ_FORMS of    *)
(* Baker/quadint_main.ml).                                                   *)
(*                                                                           *)
(* Main results: the definitions qf_reduced, form_classno, qdisc, prin_form, *)
(* prin_rep; the general forms qform, qform_rep with QFORM_PRIN,             *)
(* QFORM_REP_PRIN (prin_form and prin_rep as instances).                     *)
(*                                                                           *)
(* Uses: only the core of HOL Light (integer arithmetic over int).           *)
(*                                                                           *)
(* The first of the four imaginary quadratic base files at the end of        *)
(* section 5 (with Baker/quadint_defs.ml, Baker/quadint_ant.ml and           *)
(* Baker/quadint_ring.ml); qdisc is used by Baker/quadint_ant.ml, the        *)
(* definitions by sections 15, 16 and 22 (the class number problems).        *)
(* ========================================================================= *)

prioritize_real();;
prioritize_num();;

(* Reduced positive definite binary quadratic forms a x^2 + b x y + c y^2    *)
(* (Lagrange-Gauss): |b| <= a <= c, and b >= 0 if |b| = a or a = c.          *)

let qf_reduced = new_definition
 `qf_reduced (a:int) (b:int) (c:int) <=>
    &0 < a /\ abs b <= a /\ a <= c /\ ((abs b = a \/ a = c) ==> &0 <= b)`;;

(* Gauss: the class number of the discriminant D is the number of reduced    *)
(* primitive forms of discriminant D (0 for D >= 0: no reduced forms).       *)

let form_classno = new_definition
 `form_classno (D:int) =
    CARD {(a,b,c) | qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
                    gcd(a,gcd(b,c)) = &1}`;;

(* The discriminant of Q(sqrt(-d)) for squarefree d.                         *)

let qdisc = new_definition
 `qdisc (d:num) = if d MOD 4 = 3 then --(&d:int) else --(&4 * &d:int)`;;

(* The principal form of discriminant -d (d = 3 mod 4) and its               *)
(* representation numbers.                                                   *)

let prin_form = new_definition
 `prin_form (d:num) (x:int) (y:int) =
    x pow 2 + x * y + &((d + 1) DIV 4) * y pow 2`;;


let prin_rep = new_definition
 `prin_rep (d:num) (l:num) = CARD {(x,y) | prin_form d x y = &l}`;;

(* General binary quadratic forms qform a b c x y = a x^2 + b x y + c y^2    *)
(* and their representation numbers (finite for positive definite forms);    *)
(* the principal form is qform 1 1 ((d + 1) DIV 4).                          *)

let qform = new_definition
 `qform (a:int) (b:int) (c:int) (x:int) (y:int) =
    a * x pow 2 + b * x * y + c * y pow 2`;;

let qform_rep = new_definition
 `qform_rep (a:int) (b:int) (c:int) (l:num) =
    CARD {(x,y) | qform a b c x y = &l}`;;

let QFORM_PRIN = prove
 (`!d x y. qform (&1) (&1) (&((d + 1) DIV 4)) x y = prin_form d x y`,
  REWRITE_TAC[qform; prin_form; INT_MUL_LID]);;

let QFORM_REP_PRIN = prove
 (`!d l. qform_rep (&1) (&1) (&((d + 1) DIV 4)) l = prin_rep d l`,
  REWRITE_TAC[qform_rep; prin_rep; QFORM_PRIN]);;
