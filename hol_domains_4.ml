(* ========================================================================= *)
(* Support for running HOL Light on several OCaml domains (OCaml 4 version). *)
(* ========================================================================= *)

(* Built as Hol_domains before OCaml 5, where HOL Light runs on one domain.  *)
(* Nothing here changes what HOL Light did before. with_lock just calls f,   *)
(* so the kernel is not protected against several systhreads; counter        *)
(* uses a plain reference; and local makes one value for the program.        *)

type lock = unit;;

let new_lock () : lock = ();;

let with_lock (_ : lock) (f : unit -> 'a) : 'a = f ();;

let counter () : int -> int =
  let n = ref 0 in
  fun k -> let m = !n in (n := m + k; m);;

let local (f : unit -> 'a) : unit -> 'a =
  let v = f () in
  fun () -> v;;

let std_formatter () = Format.std_formatter;;
