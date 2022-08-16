(* ========================================================================= *)
(* Convenient library functions.                                             *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

let fail() = failwith "";;

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

let curry f x y = f(x,y);;

let uncurry f(x,y) = f x y;;

let I x = x;;

let K x y = x;;

let C f x y = f y x;;

let W f x = f x x;;

let (o) = fun f g x -> f(g x);;

let (F_F) = fun f g (x,y) -> (f x,g y);;

let (|>) = fun x f -> f x;;

(* ------------------------------------------------------------------------- *)
(* List basics.                                                              *)
(* ------------------------------------------------------------------------- *)

let hd l =
  match l with
   h::t -> h
  | _ -> failwith "hd";;

let tl l =
  match l with
   h::t -> t
  | _ -> failwith "tl";;

let map f =
  let rec mapf l =
    match l with
      [] -> []
    | (x::t) -> let y = f x in y::(mapf t) in
  mapf;;

let rec last l =
  match l with
    [x] -> x
  | (h::t) -> last t
  | [] -> failwith "last";;

let rec butlast l =
  match l with
    [_] -> []
  | (h::t) -> h::(butlast t)
  | [] -> failwith "butlast";;

let rec el n l =
  if n = 0 then hd l else el (n - 1) (tl l);;

let rec rev acc l =
  match l with
    [] -> acc
  | h::t -> rev (h::acc) t;;
let rev l = rev [] l;;

let rec map2 f l1 l2 =
  match (l1,l2) with
    [],[] -> []
  | (h1::t1),(h2::t2) -> let h = f h1 h2 in h::(map2 f t1 t2)
  | _ -> failwith "map2: length mismatch";;

(* ------------------------------------------------------------------------- *)
(* Attempting function or predicate applications.                            *)
(* ------------------------------------------------------------------------- *)

let can f x = try (f x; true) with Failure _ -> false;;

let check p x = if p x then x else failwith "check";;

(* ------------------------------------------------------------------------- *)
(* Repetition of a function.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;

let rec repeat f x =
  try let y = f x in repeat f y with Failure _ -> x;;

(* ------------------------------------------------------------------------- *)
(* To avoid consing in various situations, we propagate this exception.      *)
(* I should probably eliminate this and use pointer EQ tests instead.        *)
(* ------------------------------------------------------------------------- *)

exception Unchanged;;

let pp_exn e =
  match e with
  | Unchanged -> Pretty_printer.token "Unchanged"
  | _ -> pp_exn e;;

(* ------------------------------------------------------------------------- *)
(* Various versions of list iteration.                                       *)
(* ------------------------------------------------------------------------- *)

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec rev_itlist f l b =
  match l with
    [] -> b
  | (h::t) -> rev_itlist f t (f h b);;

let rec end_itlist f l =
  match l with
        []     -> failwith "end_itlist"
      | [x]    -> x
      | (h::t) -> f h (end_itlist f t);;

let rec itlist2 f l1 l2 b =
  match (l1,l2) with
    ([],[]) -> b
  | (h1::t1,h2::t2) -> f h1 h2 (itlist2 f t1 t2 b)
  | _ -> failwith "itlist2";;

let rec rev_itlist2 f l1 l2 b =
   match (l1,l2) with
     ([],[]) -> b
   | (h1::t1,h2::t2) -> rev_itlist2 f t1 t2 (f h1 h2 b)
      | _ -> failwith "rev_itlist2";;

(* ------------------------------------------------------------------------- *)
(* Iterative splitting (list) and stripping (tree) via destructor.           *)
(* ------------------------------------------------------------------------- *)

let rec splitlist dest x =
  try let l,r = dest x in
      let ls,res = splitlist dest r in
      (l::ls,res)
  with Failure _ -> ([],x);;

let rev_splitlist dest =
  let rec rsplist ls x =
    try let l,r = dest x in
        rsplist (r::ls) l
    with Failure _ -> (x,ls) in
  fun x -> rsplist [] x;;

let striplist dest =
  let rec strip x acc =
    try let l,r = dest x in
        strip l (strip r acc)
    with Failure _ -> x::acc in
  fun x -> strip x [];;

(* ------------------------------------------------------------------------- *)
(* Apply a destructor as many times as elements in list.                     *)
(* ------------------------------------------------------------------------- *)

let rec nsplit dest clist x =
  if clist = [] then [],x else
  let l,r = dest x in
  let ll,y = nsplit dest (tl clist) r in
  l::ll,y;;

(* ------------------------------------------------------------------------- *)
(* Replication and sequences.                                                *)
(* ------------------------------------------------------------------------- *)

let rec replicate x n =
    if n < 1 then []
    else x::(replicate x (n - 1));;

let rec (--) m n = if m > n then [] else m::((m + 1) -- n);;

(* ------------------------------------------------------------------------- *)
(* Various useful list operations.                                           *)
(* ------------------------------------------------------------------------- *)

let rec forall p l =
  match l with
    [] -> true
  | h::t -> p(h) && forall p t;;

let rec forall2 p l1 l2 =
  match (l1,l2) with
    [],[] -> true
  | (h1::t1,h2::t2) -> p h1 h2 && forall2 p t1 t2
  | _ -> false;;

let rec exists p l =
  match l with
    [] -> false
  | h::t -> p(h) || exists p t;;

let rec length k l =
  if l = [] then k else length (k + 1) (tl l);;
let length l = length 0 l;;

let rec filter p l =
  match l with
    [] -> l
  | h::t -> let t' = filter p t in
            if p(h) then if t'==t then l else h::t'
            else t';;

let rec partition p l =
  match l with
    [] -> [],l
  | h::t -> let yes,no = partition p t in
            if p(h) then (if yes == t then l,[] else h::yes,no)
            else (if no == t then [],l else yes,h::no);;

let rec mapfilter f l =
  match l with
    [] -> []
  | (h::t) -> let rest = mapfilter f t in
              try (f h)::rest with Failure _ -> rest;;

let rec find p l =
  match l with
      [] -> failwith "find"
    | (h::t) -> if p(h) then h else find p t;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;

let flat l = itlist (@) l [];;

let rec remove p l =
  match l with
    [] -> failwith "remove"
  | (h::t) -> if p(h) then h,t else
              let y,n = remove p t in y,h::n;;

let rec chop_list n l =
  if n = 0 then [],l else
  try let m,l' = chop_list (n-1) (tl l) in (hd l)::m,l'
  with Failure _ -> failwith "chop_list";;

let index x =
  let rec ind n l =
    match l with
      [] -> failwith "index"
    | (h::t) -> if x = h then n else ind (n + 1) t in
  ind 0;;

(* ------------------------------------------------------------------------- *)
(* "Set" operations on lists.                                                *)
(* ------------------------------------------------------------------------- *)

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> x = h || mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let unions l = itlist union l [];;

let intersect l1 l2 = filter (fun x -> mem x l2) l1;;

let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1;;

let subset l1 l2 = forall (fun t -> mem t l2) l1;;

let set_eq l1 l2 = subset l1 l2 && subset l2 l1;;

(* ------------------------------------------------------------------------- *)
(* Association lists.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec assoc a l =
  match l with
    (x,y)::t -> if x = a then y else assoc a t
  | [] -> failwith "find";;

let rec rev_assoc a l =
  match l with
    (x,y)::t -> if y = a then x else rev_assoc a t
  | [] -> failwith "find";;

(* ------------------------------------------------------------------------- *)
(* Zipping, unzipping etc.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let rec unzip xs =
  match xs with
  | [] -> [],[]
  | ((a,b)::rest) -> let alist,blist = unzip rest in
                     (a::alist,b::blist);;

(* ------------------------------------------------------------------------- *)
(* Sharing out a list according to pattern in list-of-lists.                 *)
(* ------------------------------------------------------------------------- *)

let rec shareout pat all =
  if pat = [] then [] else
  let l,r = chop_list (length (hd pat)) all in
  l::(shareout (tl pat) r);;

(* ------------------------------------------------------------------------- *)
(* Iterating functions over lists.                                           *)
(* ------------------------------------------------------------------------- *)

let rec do_list f l =
  match l with
    [] -> ()
  | (h::t) -> (f h; do_list f t);;

(* ------------------------------------------------------------------------- *)
(* Sorting.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec sort cmp lis =
  match lis with
    [] -> []
  | piv::rest ->
      let r,l = partition (cmp piv) rest in
      (sort cmp l) @ (piv::(sort cmp r));;

(* ------------------------------------------------------------------------- *)
(* Removing adjacent (NB!) equal elements from list.                         *)
(* ------------------------------------------------------------------------- *)

let rec uniq l =
  match l with
    x::(y::_ as t) -> let t' = uniq t in
                      if x = y then t' else
                      if t'==t then l else x::t'
 | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Convert list into set by eliminating duplicates.                          *)
(* ------------------------------------------------------------------------- *)

let setify (<=) s = uniq (sort (fun x y -> x <= y) s);;

(* ------------------------------------------------------------------------- *)
(* String operations (surely there is a better way...)                       *)
(* ------------------------------------------------------------------------- *)

let implode  = String.concat;;
  (* Woah: *)
  (* itlist (^) l "";; *)

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.substring s n 1)::l) in
  exap (String.size s - 1) [];;

(* ------------------------------------------------------------------------- *)
(* Greatest common divisor.                                                  *)
(* ------------------------------------------------------------------------- *)

let gcd = Int.gcd;;

(*
let gcd =
  let rec gxd x y =
    if y = 0 then x else gxd y (x mod y) in
  fun x y -> let x' = abs x and y' = abs y in
              if x' < y' then gxd y' x' else gxd x' y';;
*)

(* ------------------------------------------------------------------------- *)
(* Some useful functions on "num" type.                                      *)
(* ------------------------------------------------------------------------- *)

let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2
and num_10 = Int 10;;

let pow2 n = power_num num_2 (Int n);;
let pow10 n = power_num num_10 (Int n);;

let numdom r = (Num.numerator r, Num.denominator r);;

let lcm_num x y =
  if x =/ num_0 && y =/ num_0 then num_0
  else abs_num((x */ y) // gcd_num x y);;

(* ------------------------------------------------------------------------- *)
(* All pairs arising from applying a function over two lists.                *)
(* ------------------------------------------------------------------------- *)

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* Issue a report with a newline.                                            *)
(* ------------------------------------------------------------------------- *)

let report s =
  print s; print "\n";;

(* ------------------------------------------------------------------------- *)
(* Convenient function for issuing a warning.                                *)
(* ------------------------------------------------------------------------- *)

let warn cond s =
  if cond then report ("Warning: "^s) else ();;

(* ------------------------------------------------------------------------- *)
(* Flags to switch on verbose mode.                                          *)
(* ------------------------------------------------------------------------- *)

let verbose = ref true;;
let report_timing = ref true;;

(* ------------------------------------------------------------------------- *)
(* Switchable version of "report".                                           *)
(* ------------------------------------------------------------------------- *)

let remark s =
  if !verbose then report s else ();;

(* ------------------------------------------------------------------------- *)
(* Time a function.                                                          *)
(* ------------------------------------------------------------------------- *)

let time f x =
  if not (!report_timing) then f x else
  let start_time = (* Sys.time() *) Double.fromString "0.0" in
  try let result = f x in
      let finish_time = (* Sys.time()*) Double.fromString "0.0" in
      report("CPU time (user): "^(string_of_float(finish_time -. start_time)));
      result
  with e ->
      let finish_time = Double.fromString "0.0" (* Sys.time() *) in
      print("Failed after (user) CPU time of "^
            (string_of_float(finish_time -. start_time))^": ");
      raise e;;

(* ------------------------------------------------------------------------- *)
(* Versions of assoc and rev_assoc with default rather than failure.         *)
(* ------------------------------------------------------------------------- *)

let rec assocd a l d =
  match l with
    [] -> d
  | (x,y)::t -> if x = a then y else assocd a t d;;

let rec rev_assocd a l d =
  match l with
    [] -> d
  | (x,y)::t -> if y = a then x else rev_assocd a t d;;

(* ------------------------------------------------------------------------- *)
(* Version of map that avoids rebuilding unchanged subterms.                 *)
(* ------------------------------------------------------------------------- *)

let rec qmap f l =
  match l with
    h::t -> let h' = f h and t' = qmap f t in
            if h' == h && t' == t then l else h'::t'
  | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Merging and bottom-up mergesort.                                          *)
(* ------------------------------------------------------------------------- *)

let rec merge ord l1 l2 =
  match l1 with
    [] -> l2
  | h1::t1 -> match l2 with
                [] -> l1
              | h2::t2 -> if ord h1 h2 then h1::(merge ord t1 l2)
                          else h2::(merge ord l1 t2);;

let mergesort ord =
  let rec mergepairs l1 l2 =
    match (l1,l2) with
        ([s],[]) -> s
      | (l,[]) -> mergepairs [] l
      | (l,[s1]) -> mergepairs (s1::l) []
      | (l,(s1::s2::ss)) -> mergepairs ((merge ord s1 s2)::l) ss in
  fun l -> if l = [] then [] else mergepairs [] (map (fun x -> [x]) l);;

(* ------------------------------------------------------------------------- *)
(* Common measure predicates to use with "sort".                             *)
(* ------------------------------------------------------------------------- *)

(* TODO These seem like they're not in use *)

let increasing (<) f x y = f x < f y;;

let decreasing (>) f x y = f x > f y;;

(* ------------------------------------------------------------------------- *)
(* Polymorphic finite partial functions via Patricia trees.                  *)
(*                                                                           *)
(* The point of this strange representation is that it is canonical (equal   *)
(* functions have the same encoding) yet reasonably efficient on average.    *)
(*                                                                           *)
(* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
(* ------------------------------------------------------------------------- *)

(* OA:
     I can't map anything I want into an integer, but I can attach a comparison
     function to the tree. You loose the canonicity property described above
     but you'll probably always use the same comparison functions for the same
     types, anyway, if you need to compare functions.
 *)

type ('a,'b) func = Func of ('a -> 'a -> ordering) * ('a * 'b) list;;

let pp_func pk pv (Func (cmp, f)) =
  Pretty_printer.app_block "func"
    [Pretty_printer.pp_list (fun (k, v) ->
      Pretty_printer.tuple [pk k; pv v]) f];;

(* ------------------------------------------------------------------------- *)
(* Undefined function.                                                       *)
(* ------------------------------------------------------------------------- *)

let undefined cmp = Func (cmp, []);;

(* ------------------------------------------------------------------------- *)
(* In case of equality comparison worries, better use this.                  *)
(* ------------------------------------------------------------------------- *)

let is_undefined (Func (_, f)) =
  match f with
    [] -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Operation analagous to "map" for lists.                                   *)
(* ------------------------------------------------------------------------- *)

let mapf f (Func (cmp, t)) = Func (cmp, map (I F_F f) t);;

(* ------------------------------------------------------------------------- *)
(* Operations analogous to "fold" for lists.                                 *)
(* ------------------------------------------------------------------------- *)

let rec foldl f a =
  function [] -> a
         | (x,y)::xs -> foldl f (f a x y) xs;;
let foldl f a (Func (_, t)) = foldl f a t;;

let rec foldr f a =
  function [] -> a
         | (x,y)::xs -> f x y (foldr f a xs);;
let foldr f (Func (_, t)) a = foldr f a t;;

(* ------------------------------------------------------------------------- *)
(* Mapping to sorted-list representation of the graph, domain and range.     *)
(* ------------------------------------------------------------------------- *)

let graph (Func (cmp, t)) vcmp =
  setify (fun x y -> Pair.compare cmp vcmp x y <> Greater) t;;

let dom (Func (cmp, t)) =
  setify (fun x y -> cmp x y <> Greater) (map fst t);;

let ran (Func (cmp, t)) vcmp =
  setify (fun x y -> vcmp x y <> Greater) (map snd t);;

(* ------------------------------------------------------------------------- *)
(* Application.                                                              *)
(* ------------------------------------------------------------------------- *)

let applyd (Func (cmp, f)) d x' =
  let rec look t =
    match t with
    | [] -> d x'
    | (x,y)::xs ->
        match cmp x' x with
        | Less -> d x'
        | Greater -> look xs
        | Equal -> y in
  look f;;

let apply f = applyd f (fun x -> failwith "apply");;

let tryapplyd f a d = applyd f (fun x -> d) a;;

let defined f x = try apply f x; true with Failure _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Undefinition.                                                             *)
(* ------------------------------------------------------------------------- *)

let rec undefine x' cmp t =
  match t with
  | [] -> t
  | (x,y)::xs ->
      match cmp x' x with
      | Equal -> xs
      | Less -> t
      | Greater -> (x,y)::undefine x' cmp xs;;
let undefine x' (Func (cmp, t)) = Func (cmp, undefine x' cmp t);;

(* ------------------------------------------------------------------------- *)
(* Redefinition and combination.                                             *)
(* ------------------------------------------------------------------------- *)

let (|->) x y (Func (cmp, t)) =
  let rec ins x y t =
    match t with
    | [] -> [(x,y)]
    | (x',y')::xs ->
        match cmp x x' with
        | Less -> (x,y)::t
        | Greater -> (x',y')::ins x y xs
        | Equal -> (x,y)::xs in
  Func (cmp, ins x y t);;

let combine op z (Func (cmp, t1)) (Func (_, t2)) =
  let rec combine l1 l2 =
    match l1, l2 with
    | [], _ -> l2
    | _, [] -> l1
    | (x1,y1)::t1, (x2,y2)::t2 ->
        match cmp x1 x2 with
        | Less -> (x1,y1)::combine t1 l2
        | Greater -> (x2,y2)::combine l1 t2
        | Equal ->
            let y = op y1 y2 in
            let t = combine t1 t2 in
            if z y then t else (x1,y)::t in
  Func (cmp, combine t1 t2);;

(* ------------------------------------------------------------------------- *)
(* Special case of point function.                                           *)
(* ------------------------------------------------------------------------- *)

let (|=>) = fun x y cmp -> (x |-> y) (undefined cmp);;

(* ------------------------------------------------------------------------- *)
(* Grab an arbitrary element.                                                *)
(* ------------------------------------------------------------------------- *)

let choose (Func (_, t)) =
  try hd t
  with Failure _ ->
    failwith "choose: completely undefined function";;

(* ------------------------------------------------------------------------- *)
(* Install a trivial printer for the general polymorphic case.               *)
(* ------------------------------------------------------------------------- *)

(* Can't do it. *)

(* ------------------------------------------------------------------------- *)
(* Set operations parametrized by equality (from Steven Obua).               *)
(* ------------------------------------------------------------------------- *)

let rec mem' eq =
  let rec mem x lis =
    match lis with
      [] -> false
    | (h::t) -> eq x h || mem x t
  in mem;;

let insert' eq x l =
  if mem' eq x l then l else x::l;;

let union' eq l1 l2 = itlist (insert' eq) l1 l2;;

let unions' eq l = itlist (union' eq) l [];;

let subtract' eq l1 l2 = filter (fun x -> not (mem' eq x l2)) l1;;

(* ------------------------------------------------------------------------- *)
(* Accepts decimal, hex or binary numeral, using C notation 0x... for hex    *)
(* and analogous 0b... for binary.                                           *)
(* ------------------------------------------------------------------------- *)

let num_of_string =
  let values =
   ["0",0; "1",1; "2",2; "3",3; "4",4;
    "5",5; "6",6; "7",7; "8",8; "9",9;
    "a",10; "A",10; "b",11; "B",11;
    "c",12; "C",12; "d",13; "D",13;
    "e",14; "E",14; "f",15; "F",15] in
  let valof b s =
    let v = Int(assoc s values) in
    if v </ b then v else failwith "num_of_string: invalid digit for base"
  and two = num_2 and ten = num_10 and sixteen = Int 16 in
  let rec num_of_stringlist b l =
    match l with
      [] -> failwith "num_of_string: no digits after base indicator"
    | [h] -> valof b h
    | h::t -> valof b h +/ b */ num_of_stringlist b t in
  fun s ->
    match explode(s) with
        [] -> failwith "num_of_string: no digits"
      | "0"::"x"::hexdigits -> num_of_stringlist sixteen (rev hexdigits)
      | "0"::"b"::bindigits -> num_of_stringlist two (rev bindigits)
      | decdigits -> num_of_stringlist ten (rev decdigits);;

(* ------------------------------------------------------------------------- *)
(* Convenient conversion between files and (lists of) strings.               *)
(* ------------------------------------------------------------------------- *)

let strings_of_file filename =
  let fd = try Text_io.b_openIn filename
           with Text_io.Bad_file_name ->
             failwith("strings_of_file: can't open "^filename) in
  let rec suck_lines acc =
    match Text_io.b_inputLine fd with
    | Some l -> suck_lines (l::acc)
    | None -> rev acc in
  let data = suck_lines [] in
  Text_io.b_closeIn fd; data;;

let string_of_file filename =
  end_itlist (fun s t -> s^"\n"^t) (strings_of_file filename);;

let file_of_string filename s =
  let fd = Text_io.openOut filename in
  Text_io.output fd s; Text_io.closeOut fd;;
