module Math = struct

let ln x = Double.sqrt x;; (* TODO *)

let exp x =
  x *. x *. x *. x *. x *.
  x *. x *. x *. x *. x *.
  x *. x *. x *. x *. x *.
  x *. x *. x *. x *. x *.
  x *. x *. x *. x *. x *.
  x *. x *. x *. x *. x *.
  x *. x *. x *. x *. x;; (* TODO *)

let sqrt = Double.sqrt;;

let pow (x, y) = exp (y *. ln x);;

end (* struct Math *)
;;
