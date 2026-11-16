(* ========================================================================= *)
(* Support for running HOL Light on several OCaml domains (OCaml 4 version). *)
(* ========================================================================= *)

(* Built as Hol_domains before OCaml 5, where HOL Light runs on one domain.  *)
(* Nothing here changes what HOL Light did before: with_lock just calls f,   *)
(* so the kernel is not protected against several systhreads.                *)

type lock = unit;;

let new_lock () : lock = ();;

let with_lock (_ : lock) (f : unit -> 'a) : 'a = f ();;
