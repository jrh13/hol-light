(* ------------------------------------------------------------------------- *)
(* Load in the bignum library.                                               *)
(* ------------------------------------------------------------------------- *)

include Num;;

let num = Num.num_of_int;;

module NumExt = struct
  let numdom (r:num):num * num =
    let r' = Ratio.normalize_ratio (ratio_of_num r) in
    num_of_big_int(Ratio.numerator_ratio r'),
    num_of_big_int(Ratio.denominator_ratio r');;

  let gcd_num (n1:num) (n2:num): num =
    num_of_big_int(Big_int.gcd_big_int (big_int_of_num n1) (big_int_of_num n2));;
end;;

include NumExt;;
