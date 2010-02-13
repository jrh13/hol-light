(******************************************************************************)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : July 2009                                                  *)
(******************************************************************************)

let paths = [".";!hol_dir ^ "/Boyer_Moore"]
in map (fun st -> load_on_path paths st)
        ["support.ml";
         "struct_equal.ml";
         "shells.ml";
         "environment.ml";
         "clausal_form.ml";
         "waterfall.ml";
         "rewrite_rules.ml";
         "definitions.ml";
         "terms_and_clauses.ml";
         "equalities.ml";
         "induction.ml";
	 "counterexample.ml";
         "generalize.ml";
         "irrelevance.ml";
         "main.ml"];;
