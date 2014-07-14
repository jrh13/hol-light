(* =========================================================== *)
(* Report functions                                            *)
(* Author: Thomas C. Hales                                     *)
(* Date: 2011-08-21                                            *)
(* =========================================================== *)

(* port of error.cc
    basic procedures to print messages to the standard output
   and to count errors.

*)

needs "verifier/interval_m/types.ml";;

module Report = struct

open Interval_types;;

let time_string () =   Printf.sprintf "time(%.0f)" (Sys.time());;

let (get_error_count,reset_error_count,inc_error_count) =
  let error_count = ref 0 in
    ((fun _ -> !error_count),(fun _ -> error_count := 0),
   (fun _ -> error_count:= !error_count + 1));;

let (get_corner_count,reset_corner_count,inc_corner_count) =
  let corner_count = ref 0 in
    ((fun _ -> !corner_count),(fun _ -> corner_count := 0),
   (fun _ -> corner_count:= !corner_count + 1));;

let diagnostic_string () =
  let d = get_error_count() in
  if (d>0) then Printf.sprintf "(errors %d)" (get_error_count())  else "(no errors)";;

let report s =
  Format.print_string s; Format.print_newline(); Format.print_flush();;

let report_timed s = report (s^" "^(time_string()));;

let report_error =
  let error_max = 25 in  (* was 200, recurse.cc had a separate counter limit at 25 *)
    fun s ->
      let ec = get_error_count() in
      (inc_error_count(); report_timed (Printf.sprintf "error(%d) --\n%s" ec s);
       Pervasives.ignore(get_error_count() < error_max or raise Fatal));;

let report_fatal s =
  ( inc_error_count(); report_timed ("error --\n"^s); raise Fatal);;

end;;
