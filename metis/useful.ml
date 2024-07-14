(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* ========================================================================= *)

module Useful = struct

(* ------------------------------------------------------------------------- *)
(* Exceptions.                                                               *)
(* ------------------------------------------------------------------------- *)

exception Error of string;;

exception Bug of string;;

let total f x = try Some (f x) with Error _ -> None;;

let isSome = function
    (Some _) -> true
  | None -> false
;;

let can f x = isSome (total f x);;

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

let cComb f x y = f y x;;

let iComb x = x;;

let kComb x y = x;;

let sComb f g x = f x (g x);;

let wComb f x = f x x;;

let rec funpow n f x = match n with
      0 -> x
    | _ -> funpow (n - 1) f (f x);;

let exp m =
      let rec f x y z = match y with
          0 -> z
        | _ -> f (m (x,x)) (Int.div y 2) (if y mod 2 = 0 then z else m (z,x))
    in
      f
    ;;

(* ------------------------------------------------------------------------- *)
(* Pairs.                                                                    *)
(* ------------------------------------------------------------------------- *)

let pair x y = (x,y);;

let swap (x,y) = (y,x);;

let curry f x y = f (x,y);;

let uncurry f (x,y) = f x y;;

(* ------------------------------------------------------------------------- *)
(* State transformers.                                                       *)
(* ------------------------------------------------------------------------- *)

let return : 'a -> 's -> 'a * 's = pair;;

let bind f (g : 'a -> 's -> 'b * 's) x = uncurry g (f x);;

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

let revCompare cmp x_y =
    match cmp x_y with Less -> Greater | Equal -> Equal | Greater -> Less;;

let prodCompare xCmp yCmp ((x1,y1),(x2,y2)) =
    match xCmp (x1,x2) with
      Less -> Less
    | Equal -> yCmp (y1,y2)
    | Greater -> Greater;;

let lexCompare cmp =
      let rec lex = function
          ([],[]) -> Equal
        | ([], _ :: _) -> Less
        | (_ :: _, []) -> Greater
        | (x :: xs, y :: ys) ->
          (match cmp (x,y) with
            Less -> Less
          | Equal -> lex (xs,ys)
          | Greater -> Greater)
    in
      lex
    ;;

let boolCompare = function
    (false,true) -> Less
  | (true,false) -> Greater
  | _ -> Equal;;

(* ------------------------------------------------------------------------- *)
(* Lists.                                                                    *)
(* ------------------------------------------------------------------------- *)

let rec first f = function
    [] -> None
  | (x :: xs) -> (match f x with None -> first f xs | s -> s);;

let rec maps (f : 'a -> 's -> 'b * 's) = function
    [] -> return []
  | (x :: xs) ->
    bind (f x) (fun y -> bind (maps f xs) (fun ys -> return (y :: ys)));;

let zipWith f =
    let rec z l = function
          ([], []) -> l
        | (x :: xs, y :: ys) -> z (f x y :: l) (xs, ys)
        | _ -> raise (Error "zipWith: lists different lengths")
    in
      fun xs -> fun ys -> List.rev (z [] (xs, ys))
    ;;

let zip xs ys = zipWith pair xs ys;;

let unzip ab =
  let inc ((x,y),(xs,ys)) = (x :: xs, y :: ys)
  in Mlist.foldl inc ([],[]) (List.rev ab);;

let enumerate l = fst (maps (fun x m -> ((m, x), m + 1)) l 0);;

let revDivide l =
  let rec revDiv acc = function
      (l, 0) -> (acc,l)
    | ([], _) -> raise Subscript
    | (h :: t, n) -> revDiv (h :: acc) (t, n - 1)
  in fun n -> revDiv [] (l, n);;

let divide l n = let (a,b) = revDivide l n in (List.rev a, b);;

let updateNth (n,x) l =
    let (a,b) = revDivide l n
    in
      match b with [] -> raise Subscript | (_ :: t) -> List.rev_append a (x :: t)
;;

let deleteNth n l =
    let (a,b) = revDivide l n
    in
      match b with [] -> raise Subscript | (_ :: t) -> List.rev_append a t
;;

(* ------------------------------------------------------------------------- *)
(* Sets implemented with lists.                                              *)
(* ------------------------------------------------------------------------- *)

let mem x l = List.mem x l;;

(* ------------------------------------------------------------------------- *)
(* Strings.                                                                  *)
(* ------------------------------------------------------------------------- *)

let mkPrefix p s = p ^ s

let stripSuffix pred s =
  let rec strip pos =
    if pos < 0 then "" else
    if pred (s.[pos]) then strip (pos - 1)
    else String.sub s 0 (pos + 1)
  in strip (String.length s - 1);;

(* ------------------------------------------------------------------------- *)
(* Sorting and searching.                                                    *)
(* ------------------------------------------------------------------------- *)

let sort cmp = List.sort (fromCompare cmp);;

let sortMap f cmp = function
    [] -> []
  | ([_] as l) -> l
  | xs ->
      let ncmp ((m,_),(n,_)) = cmp (m,n)
      in let nxs = List.map (fun x -> (f x, x)) xs
      in let nys = List.sort (fromCompare ncmp) nxs
    in
      List.map snd nys
    ;;

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

let rec interval m = function
    0 -> []
  | len -> m :: interval (m + 1) (len - 1);;

let divides = function
    (_, 0) -> true
  | (0, _) -> false
  | (a, b) -> b mod (Int.abs a) = 0;;
let divides = curry divides;;

(* ------------------------------------------------------------------------- *)
(* Useful impure features.                                                   *)
(* ------------------------------------------------------------------------- *)

let generator = ref 0;;

  let newIntThunk () =
      let n = !generator
      in generator := n + 1;
        n
      ;;

  let newIntsThunk k () =
      let
        n = !generator

        in generator := n + k;
          interval n k
      ;;

  let newInt () = newIntThunk ();;

  let newInts k =
      if k <= 0 then []
      else (newIntsThunk k) ();;

end

