(*
 This file contains specifications of the SAT tools that
 can be invoked from HOL.
 Details of format in the comments following each field name.

 {name            (* solver name                                         *)
  url,            (* source for downloading                              *)
  executable,     (* path to executable                                  *)
  good_exit,      (* code return upon normal termination                 *)
  notime_run,     (* command to invoke solver on a file                  *)
  time_run,       (* command to invoke on a file and time                *)
  only_true       (* true if only the true atoms are listed in models    *)
  failure_string, (* string whose presence indicates unsatisfiability    *)
  start_string,   (* string signalling start of variable assignment      *)
  end_string}     (* string signalling end of variable assignment        *)
*)

type sat_solver =
  {name           : string;
   url            : string;
   executable     : string;
   good_exit      : int;
   notime_run     : string -> string * string -> string;
   time_run       : string -> (string * string) * int -> string;
   only_true      : bool;
   failure_string : string;
   start_string   : string;
   end_string     : string}

let zchaff =
  {name           = "zchaff";
   url            =
    "http://www.ee.princeton.edu/~chaff/zchaff/zchaff.2001.2.17.linux.gz";
   executable     = "zchaff";
   good_exit      = 0;
   notime_run     = (fun ex -> fun (infile,outfile) ->
                  (ex ^ " " ^ infile ^ " > " ^ outfile ^
                   "; zc2mso " ^ infile ^
                   " -m " ^ outfile ^ ".proof -z "^
                   (Filename.concat (!temp_path) "resolve_trace")^
                   "> "^
                   (Filename.concat (!temp_path) "zc2mso_trace")));
   time_run       = (fun ex -> fun ((infile,outfile),time) ->
                      (ex ^ " " ^ infile ^ " " ^ (string_of_int time) ^ " > " ^ outfile));
   only_true      = false;
   failure_string = "UNSAT";
   start_string   = "Instance Satisfiable";
   end_string     = "Random Seed Used"}

let minisat =
  {name           = "minisat";
   url            = "http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/cgi/MiniSat_v1.13_linux.cgi";
   executable     = "minisat";
   good_exit      = 10;
   notime_run     = (fun ex -> fun (infile,outfile) ->
                      (ex ^ " -r " ^ outfile ^" "^ infile ^ " > " ^ outfile ^".stats"));
   time_run       = (fun ex -> fun ((infile,outfile),time) ->
                      (ex ^ " " ^ infile ^ " " ^ (string_of_int time) ^ " > " ^ outfile));
   only_true      = false;
   failure_string = "UNSAT";
   start_string   = "v";
   end_string     = "0"}

let minisatp =
  {name           = "minisatp";
   url            = "http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/cgi/MiniSat_v1.13_linux.cgi";
   executable     =
   (match (Sys.os_type) with
      "Win32" | "Cygwin" -> "minisat.exe"
    | _       -> "minisat");
   good_exit      = 10;
   notime_run     = (fun ex -> fun (infile,outfile) ->
                      (ex ^ " -r " ^ outfile ^ " -p " ^ outfile ^ ".proof " ^ infile ^ " > " ^ outfile ^".stats"));
   time_run       = (fun ex -> fun ((infile,outfile),time) ->
                      (ex ^ " " ^ infile ^ " " ^ (string_of_int time) ^ " > " ^ outfile));
   only_true      = false;
   failure_string = "UNSAT";
   start_string   = "SAT";
   end_string     = "0"}
