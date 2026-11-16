(* ========================================================================= *)
(* Support for running HOL Light on several OCaml domains (OCaml 5 version). *)
(* ========================================================================= *)

(* Built as Hol_domains on OCaml 5; hol_domains_4.ml is the version for      *)
(* earlier OCaml, which runs HOL Light on one domain.                        *)

(* with_lock l f runs f () while it holds l, and releases l however f        *)
(* ends. The kernel relies on it for soundness.                              *)

type lock = Mutex.t;;

let new_lock () : lock = Mutex.create ();;

let with_lock (l : lock) (f : unit -> 'a) : 'a =
  Mutex.lock l;
  match f () with
    r -> Mutex.unlock l; r
  | exception e -> Mutex.unlock l; raise e;;
