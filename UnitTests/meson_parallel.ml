(* ========================================================================= *)
(*            HOL LIGHT unit tests for MESON in parallel domains             *)
(*                                                                           *)
(* MESON keeps no global mutable state during a call, so independent calls   *)
(* can run in parallel OCaml 5 domains. This checks that calls made from     *)
(* several domains at once give the same results as sequential calls, and   *)
(* that genvar never returns the same variable to two domains.              *)
(*                                                                           *)
(* This file uses the Domain module, so it only compiles with OCaml 5: the   *)
(* Makefile builds UnitTests/*_parallel.ml only when OCaml 5 is used.        *)
(* ========================================================================= *)

assert (int_of_string (String.sub Sys.ocaml_version 0 1) >= 5);;

let ndomains = 4;;

(* The result of a call, so that failures can be compared too *)
type meson_result = Proved of (term list * term) | Failed;;

let run_meson (ths,tm) =
  try Proved (dest_thm (MESON ths tm)) with Failure _ -> Failed;;

(* Run every goal in each of ndomains domains (twice, each domain starting  *)
(* at a different goal), and check against the results of sequential runs. *)
let check_parallel goals =
  let goals = Array.of_list goals in
  let n = Array.length goals in
  let expected = Array.map run_meson goals in
  let worker k () =
    let out = Array.make n Failed in
    for _ = 1 to 2 do
      for j = 0 to n - 1 do
        let i = (j + k) mod n in out.(i) <- run_meson goals.(i)
      done
    done;
    out in
  let ds = map (fun k -> Domain.spawn (worker k)) (0--(ndomains-1)) in
  List.iter (fun d -> assert (Domain.join d = expected)) ds;;

let fol_goals =
  [[], `(!x. P x ==> P (f x)) /\ P a ==> P (f (f (f a)))`;
   [], `(?x. !y. R x y) ==> (!y. ?x. R x y)`;
   [], `(!x y z. R x y /\ R y z ==> R x z) /\ R a b /\ R b c /\ R c d
        ==> R a d`;
   [], `?y:A. !x. P y ==> P x`;
   [SUBSET; IN_UNION; IN_INTER], `s SUBSET t ==> s INTER u SUBSET t UNION v`;
   [ADD_SYM; ADD_ASSOC], `a + b + c = c + b + (a:num)`;
   [], `(P:A->bool) a ==> P b`];;              (* Not a theorem: fails *)

let equality_goals =
  [[], `(!x:A. f(f x) = x) /\ f a = b ==> f b = a`;
   [], `a:A = b /\ b = c /\ P a ==> P c`;
   [], `(!x:A. g(f x):A = x) /\ f a = f b ==> a = b`;
   [], `(!x y:A. f x y = f y x) /\ (!x. f x e = x) ==> f e a = a`];;

(* The flags are global, so they are set before the domains are spawned *)
let with_flags brand f =
  let old_verbose = !verbose and old_brand = !meson_brand in
  verbose := false; meson_brand := brand;
  let restore() = verbose := old_verbose; meson_brand := old_brand in
  (try f () with e -> (restore(); raise e));
  restore();;

with_flags false (fun () -> check_parallel (fol_goals @ equality_goals));;
with_flags true (fun () -> check_parallel equality_goals);;

(* genvar never gives the same variable to two domains *)
let _ =
  let count = 1000 in
  let ds = map (fun _ -> Domain.spawn (fun () ->
                  map (fun _ -> genvar `:bool`) (1--count)))
               (1--ndomains) in
  let gvs = List.concat (map Domain.join ds) in
  assert (length (setify gvs) = ndomains * count);;
