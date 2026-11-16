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

(* counter () gives a function next: next k returns the count and adds k     *)
(* to it, in one atomic step. The count starts at 0.                         *)

let counter () : int -> int =
  let n = Atomic.make 0 in
  fun k -> Atomic.fetch_and_add n k;;

(* local f gives a function get: get () returns the calling domain's own     *)
(* value, which f () makes on the first call in that domain. It is here,     *)
(* not in the files that camlp5 reads, as pa_j misreads Domain.DLS.          *)

let local (f : unit -> 'a) : unit -> 'a =
  let key = Domain.DLS.new_key f in
  fun () -> Domain.DLS.get key;;

(* The calling domain's standard formatter. Format.std_formatter is that     *)
(* of the first domain only.                                                 *)

let std_formatter () = Format.get_std_formatter ();;
