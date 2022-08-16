(*
  This module attempts to provide a compatibility interface for the
  OCaml num library, which HOL Light uses.
 *)

module type NUM = sig

  val num_of_int : int -> num
  val int_of_num : num -> int
  val string_of_num : num -> string

  val denominator : num -> num
  val numerator : num -> num

  val abs_num : num -> num
  val floor_num : num -> num

  val ( +/ ) : num -> num -> num
  val ( -/ ) : num -> num -> num
  val ( */ ) : num -> num -> num
  val ( // ) : num -> num -> num

  val add_num : num -> num -> num
  val sub_num : num -> num -> num
  val mul_num : num -> num -> num
  val div_num : num -> num -> num
  val minus_num : num -> num

  (* These operations are for integers (unit denominator) *)

  val quo_num : num -> num -> num
  val mod_num : num -> num -> num

  val ( </ ): num -> num -> bool
  val ( >/ ) : num -> num -> bool
  val ( <=/ ) : num -> num -> bool
  val ( >=/ ) : num -> num -> bool
  val ( =/ ) : num -> num -> bool
  val ( <>/ ) : num -> num -> bool
  val le_num : num -> num -> bool
  val lt_num : num -> num -> bool
  val ge_num : num -> num -> bool
  val gt_num : num -> num -> bool
  val eq_num : num -> num -> bool

  val min_num : num -> num -> num
  val max_num : num -> num -> num
  val compare : num -> num -> order
  val gcd_num : num -> num -> num

  val ( **/) : num -> num -> num
  val power_num : num -> num -> num

  val is_integer_num : num -> bool;;

end;;

type num =
  | Int of int
  | Rat of rat
;;

let pp_num n =
  match n with
  | Int i -> pp_int i
  | Rat r -> pp_rat r
;;

module Num (* : NUM*) = struct

type num = num;;

let denominator n =
  match n with
  | Int i -> Int 1
  | Rat r -> Int (Rat.denominator r)
;;

let numerator n =
  match n with
  | Int i -> n
  | Rat r -> Int (Rat.numerator r)
;;

let num_fix n =
  match n with
  | Int i -> n
  | Rat r ->
      if Rat.denominator r = 1 then
        Int (Rat.numerator r)
      else if Rat.denominator r = 0 then
        failwith "num_fix: division by zero"
      else n
;;

let abs_num n =
  match n with
  | Int i -> Int (abs i)
  | Rat r -> Rat (Rat.(/) (Rat.fromInt (abs (Rat.numerator r)))
                          (Rat.fromInt (Rat.denominator r)))
;;

let sign_num n =
  let sign i = if i < 0 then -1 else if i > 0 then 1 else 0 in
  match n with
  | Int i -> sign i
  | Rat r -> sign (Rat.numerator r)
;;

(* The Rat type operations normalize results *)
let norm n = num_fix n
;;

let num_of_int i = Int i
;;

let int_of_num n =
  match n with
  | Int i -> i
  | Rat r -> Rat.numerator r / Rat.denominator r
;;

let string_of_num n =
  match n with
  | Int i -> string_of_int i
  | Rat r ->
      let n = Rat.numerator r in
      let d = Rat.denominator r in
      string_of_int n ^ "/" ^ string_of_int d
;;

let minus_num n =
  match n with
  | Int i -> Int (-i)
  | Rat r -> Rat (rat_minus r)
;;

let (+/) x y =
  match x, y with
  | Int i, Int j -> Int (i + j)
  | Int i, Rat r -> Rat (Rat.(+) (Rat.fromInt i) r)
  | Rat r, Int i -> Rat (Rat.(+) r (Rat.fromInt i))
  | Rat i, Rat j -> Rat (Rat.(+) i j)
;;
let (+/) x y = num_fix (x +/ y);;
let add_num = (+/);;

let (-/) x y =
  match x, y with
  | Int i, Int j -> Int (i - j)
  | Int i, Rat r -> Rat (Rat.(-) (Rat.fromInt i) r)
  | Rat r, Int i -> Rat (Rat.(-) r (Rat.fromInt i))
  | Rat i, Rat j -> Rat (Rat.(-) i j)
;;
let (-/) x y = num_fix (x -/ y);;
let sub_num = (-/);;

let ( */) x y =
  match x, y with
  | Int i, Int j -> Int (i * j)
  | Int i, Rat r -> Rat (Rat.( * ) (Rat.fromInt i) r)
  | Rat r, Int i -> Rat (Rat.( * ) r (Rat.fromInt i))
  | Rat i, Rat j -> Rat (Rat.( * ) i j)
;;
let ( */) x y = num_fix (x */ y);;
let mul_num = ( */);;

let (//) x y =
  match x, y with
  | Int i, Int j -> Rat (Rat.(/) (Rat.fromInt i) (Rat.fromInt j))
  | Int i, Rat r -> Rat (Rat.(/) (Rat.fromInt i) r)
  | Rat r, Int i -> Rat (Rat.(/) r (Rat.fromInt i))
  | Rat i, Rat j -> Rat (Rat.(/) i j)
;;
let (//) x y = num_fix (x // y);;
let div_num = (//);;

let quo_num x y =
  match x, y with
  | Int i, Int j ->
      let q = i / j in
      let r = i mod j in
      Int (if r >= 0 then q else if j > 0 then q - 1 else q + 1)
  | Int _, Rat _ ->
      let y = abs_num y in
      Int (int_of_num (x // y))
  | _ ->
      Int (int_of_num (x // y))
;;

let is_integer_num n =
  match n with
  | Int _ -> true
  | _ -> false;;

let mod_num x y =
  match x, y with
  | Int i, Int j ->
      let r = i mod j in
      Int (if r >= 0 then r else if j > 0 then r + j else r - j)
  | _ -> x -/ (y */ quo_num x y)
;;

let power_num b e =
  let rec pow b e =
    if e < 1 then
      Int 1
    else if e mod 2 <> 0 then b */ pow b (e - 1)
    else let p = pow b (e / 2) in
           p */ p in
  pow b (int_of_num e)
;;

let ( **/) = power_num;;

let floor_num n =
  match n with
  | Int i -> n
  | Rat r -> Int (Rat.numerator r / Rat.denominator r)
;;

let compare x y =
  match x, y with
  | Int i, Int j -> Int.compare i j
  | Int i, Rat r -> Rat.compare (Rat.fromInt i) r
  | Rat r, Int j -> Rat.compare r (Rat.fromInt j)
  | Rat i, Rat j -> Rat.compare i j
;;

let ( </) x y = compare x y = Less;;
let ( <=/) x y = compare x y <> Greater;;
let ( >/) x y = compare x y = Greater;;
let ( >=/) x y = compare x y <> Less;;
let ( =/) x y = compare x y = Equal;;
let ( <>/) x y = compare x y <> Equal;;

let lt_num = ( </);;
let le_num = ( <=/);;
let gt_num = ( >/);;
let ge_num = ( >=/);;
let eq_num = ( =/);;

let min_num x y = if x <=/ y then x else y;;
let max_num x y = if x >=/ y then x else y;;
let gcd_num x y =
  match x, y with
  | Int i, Int j -> Int (abs (Int.gcd i j))
;;

let succ_num n = Int 1 +/ n;;

end;; (* struct *)

(* There's no 'open': *)

let num_of_int = Num.num_of_int;;
let int_of_num = Num.int_of_num;;
let string_of_num = Num.string_of_num;;
let denominator = Num.denominator;;
let numerator = Num.numerator;;
let minus_num = Num.minus_num;;
let abs_num = Num.abs_num;;
let floor_num = Num.floor_num;;

let ( +/ ) = Num.( +/);;
let ( -/ ) = Num.( -/);;
let ( */ ) = Num.( */);;
let ( // ) = Num.( //);;

let add_num = Num.add_num ;;
let sub_num = Num.sub_num ;;
let mul_num = Num.mul_num ;;
let div_num = Num.div_num ;;

(* These operations are for integers (unit denominator) *)

let quo_num = Num.quo_num;;
let mod_num = Num.mod_num;;

let ( </ ) = Num.( </);;
let ( >/ ) = Num.( >/);;
let ( <=/ ) = Num.( <=/);;
let ( >=/ ) = Num.( >=/);;
let ( =/ ) = Num.( =/);;
let ( <>/ ) = Num.( <>/);;

let lt_num = Num.lt_num;;
let le_num = Num.le_num;;
let gt_num = Num.gt_num;;
let ge_num = Num.ge_num;;
let eq_num = Num.eq_num;;

let min_num = Num.min_num;;
let max_num = Num.max_num;;
let compare = Num.compare;;
let gcd_num = Num.gcd_num;;

let ( **/) = Num.( **/);;
let power_num = Num.power_num;;

let is_integer_num = Num.is_integer_num;;

let succ_num = Num.succ_num;;
