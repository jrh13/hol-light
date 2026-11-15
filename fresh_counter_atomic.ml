(* ========================================================================= *)
(* Counters for generating fresh names, e.g. in genvar.                      *)
(*                                                                           *)
(* This file is compiled to fresh_counter.cmo/.cmx for OCaml 5 (see the      *)
(* Makefile, and fresh_counter_ref.ml for earlier versions), so its contents *)
(* are only visible as Fresh_counter.t, Fresh_counter.make and               *)
(* Fresh_counter.next. With OCaml 5, code can run in several domains in      *)
(* parallel, so the counter is an atomic integer: no two calls of "next"     *)
(* ever return the same number, even when they are made from different      *)
(* domains at the same time. With a single domain the behaviour is the same  *)
(* as that of an ordinary reference. The signature below is the same as in   *)
(* fresh_counter_ref.ml and keeps the type t abstract.                       *)
(* ========================================================================= *)

include (struct
  type t = int Atomic.t
  let make (n:int) : t = Atomic.make n
  let next (c:t) : int = Atomic.fetch_and_add c 1
end : sig
  type t
  val make : int -> t        (* A new counter, starting at the given value *)
  val next : t -> int        (* Return the current value and increment it  *)
end);;
