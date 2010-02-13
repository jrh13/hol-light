(* ========================================================================= *)
(* Create a standalone HOL image. Assumes that we are running under Linux    *)
(* and have the program "ckpt" available to create checkpoints.              *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

#use "hol.ml";;

(* ------------------------------------------------------------------------- *)
(* Record the build date and OCaml version for the startup banner.           *)
(* ------------------------------------------------------------------------- *)

#load "unix.cma";;

let startup_banner =
   let {Unix.tm_mday = d;Unix.tm_mon = m;Unix.tm_year = y;Unix.tm_wday = w} =
     Unix.localtime(Unix.time()) in
  let nice_date = string_of_int d ^ " " ^
    el m ["January"; "February"; "March"; "April"; "May"; "June";
          "July"; "August"; "September"; "October"; "November"; "December"] ^
    " " ^ string_of_int(1900+y) in
  "        HOL Light "^hol_version^
  ", built "^nice_date^" on OCaml "^Sys.ocaml_version;;

(* ------------------------------------------------------------------------- *)
(* Self-destruct to create checkpoint file; print banner when restarted.     *)
(* ------------------------------------------------------------------------- *)

let self_destruct bannerstring =
  let longer_banner = startup_banner ^ " with ckpt" in
  let complete_banner =
    if bannerstring = "" then longer_banner
    else longer_banner^"\n        "^bannerstring in
  (Gc.compact();
   ignore(Unix.system "sleep 1s; kill -USR1 $PPID");
   Format.print_string complete_banner;
   Format.print_newline(); Format.print_newline());;

(* ------------------------------------------------------------------------- *)
(* Non-destructive checkpoint using CryoPID "freeze".                        *)
(* ------------------------------------------------------------------------- *)

let checkpoint bannerstring =
  let rec waste_time n = if n = 0 then () else waste_time(n - 1) in
  let longer_banner = startup_banner ^ " with CryoPID" in
  let complete_banner =
    if bannerstring = "" then longer_banner
    else longer_banner^"\n        "^bannerstring in
  (Gc.compact();
   ignore(Unix.system "(sleep 1s; freeze -l hol.snapshot $PPID) &");
   waste_time 100000000;
   Format.print_string complete_banner;
   Format.print_newline(); Format.print_newline());;
