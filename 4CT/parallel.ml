(* ========================================================================= *)
(* 4CT/parallel.ml                                                           *)
(*                                                                           *)
(* Parallel evaluation in one HOL Light process, for OCaml 5 or later only   *)
(* (Domain, Atomic, Mutex).  Loading this file before make.ml (as            *)
(* make_parallel.ml does) installs the hooks of par_hook.ml, so that         *)
(* present_eval.ml evaluates the side conditions of the presentation         *)
(* scripts, and part2_run.ml the 633 configurations, in !par_domains         *)
(* domains.  Nothing else changes, and the rest of the package needs only    *)
(* OCaml 4.03.                                                               *)
(*                                                                           *)
(*   par_domains        FOURCOLOR_DOMAINS if set, else                       *)
(*                      Domain.recommended_domain_count() (the runtime       *)
(*                      starts at most 128 unless OCAMLRUNPARAM d is         *)
(*                      raised; par_map uses as many as it can start)        *)
(*   par_minor_heap     the minor heap of every domain, in words:            *)
(*                      FOURCOLOR_MINOR_HEAP if set (0 keeps the runtime's), *)
(*                      else 8M words (64 MB).  Each domain allocates about  *)
(*                      1 GB/s, and whenever one minor heap is full all      *)
(*                      domains stop for a minor collection; with the        *)
(*                      runtime's 256k words the 633 checks of Part 2 take   *)
(*                      17% longer (native, 64 domains)                      *)
(*                                                                           *)
(* par_map n f jobs claims the jobs in array order by an atomic increment    *)
(* and writes each result to its own slot, read only after Domain.join.      *)
(* Soundness does not depend on any of this: thm is abstract, and every      *)
(* theorem, in whichever domain, is built by the kernel rules of fusion.ml,  *)
(* whose only mutable state (the tables of types, constants, axioms and      *)
(* definitions) the evaluations read but never write; OCaml 5 keeps even a   *)
(* racy program memory- and type-safe.  A data race in a job could only make *)
(* the run fail, so jobs must not share mutable state, nor parse or print    *)
(* outside par_say (string_of_term shares one buffer, and the parser and     *)
(* type inference keep global counters).  Each domain's OCaml stack grows up *)
(* to the same limit as the main domain's (Gc.stack_limit).                  *)
(* ========================================================================= *)

let () =
  if int_of_string (String.sub Sys.ocaml_version 0
                      (String.index Sys.ocaml_version '.')) < 5 then
    failwith "4CT/parallel.ml needs OCaml 5 or later; use 4CT/make.ml";;

needs "4CT/par_hook.ml";;

#directory "+unix";;
#load "unix.cma";;

let par_getenv s = try Some(Sys.getenv s) with Not_found -> None;;

let par_minor_heap =
  ref (match par_getenv "FOURCOLOR_MINOR_HEAP" with
         Some s -> int_of_string s
       | None -> 8388608);;

let par_lock = Mutex.create();;

let par_locked_say f =
  Mutex.lock par_lock;
  (try f() with e -> Mutex.unlock par_lock; raise e);
  Mutex.unlock par_lock;;

let par_set_minor_heap() =
  if !par_minor_heap > 0 then
    Gc.set { (Gc.get()) with Gc.minor_heap_size = !par_minor_heap };;

let par_domain_map n f jobs =
  let m = Array.length jobs in
  let results = Array.make m None in
  let next = Atomic.make 0 in
  let worker d () =
    par_set_minor_heap();
    let rec loop() =
      let j = Atomic.fetch_and_add next 1 in
      if j < m then begin
        results.(j) <-
          (try Some(f d jobs.(j)) with e ->
             (par_locked_say (fun () ->
                Printf.printf "PAR: job %d failed in domain %d: %s\n%!" j d
                  (Printexc.to_string e));
              None));
        loop()
      end in
    loop() in
  par_set_minor_heap();
  let rec spawn d =
    if d >= min n m then [] else
    match (try Some(Domain.spawn (worker d)) with Failure _ -> None) with
      Some dom -> dom::spawn(d + 1)
    | None -> (par_locked_say (fun () ->
                 Printf.printf "PAR: only %d domains could be started\n%!" d);
               []) in
  let doms = spawn 1 in
  worker 0 ();
  List.iter Domain.join doms;
  results;;

par_domains :=
  (match par_getenv "FOURCOLOR_DOMAINS" with
     Some s -> int_of_string s
   | None -> Domain.recommended_domain_count());;
par_mapper := { par_map = par_domain_map };;
par_say := par_locked_say;;
par_time := Unix.gettimeofday;;
par_enabled := true;;
