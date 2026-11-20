(* ========================================================================= *)
(* Counters for generating fresh names, e.g. in genvar.                      *)
(*                                                                           *)
(* This file is compiled to fresh_counter.cmo/.cmx for OCaml versions before *)
(* 5 (see the Makefile, and fresh_counter_atomic.ml for OCaml 5), so its     *)
(* contents are only visible as Fresh_counter.t, Fresh_counter.make and      *)
(* Fresh_counter.next. These OCaml versions have no parallel domains (and    *)
(* possibly no Atomic module), so an ordinary reference is enough. The       *)
(* signature below is the same as in fresh_counter_atomic.ml and keeps the   *)
(* type t abstract.                                                          *)
(* ========================================================================= *)

include (struct
  type t = int ref
  let make (n:int) : t = ref n
  let next (c:t) : int = let n = !c in (c := n + 1; n)
end : sig
  type t
  val make : int -> t        (* A new counter, starting at the given value *)
  val next : t -> int        (* Return the current value and increment it  *)
end);;
