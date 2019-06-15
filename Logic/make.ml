(* ========================================================================= *)
(* Basic metatheorems for FOL without and with equality.                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Background theories.                                                      *)
(* ------------------------------------------------------------------------- *)

needs "Library/analysis.ml";;   (* Just for some "subseq" lemmas really      *)
needs "Library/wo.ml";;         (* Well-orders and Zorn's lemma equivalents  *)
needs "Library/rstc.ml";;       (* Reflexive-symmetric-transitive closures   *)
needs "Examples/reduct.ml";;    (* Abstract reduction relations.             *)
needs "Examples/multiwf.ml";;   (* Wellfoundedness of multiset ordering      *)

(* ------------------------------------------------------------------------- *)
(* Model theory of first order logic.                                        *)
(* ------------------------------------------------------------------------- *)

loadt "Logic/fol.ml";;          (* Basic first order logic definitions       *)
loadt "Logic/prenex.ml";;       (* Prenex normal form                        *)
loadt "Logic/skolem.ml";;       (* Skolem normal form                        *)
loadt "Logic/fol_prop.ml";;     (* Compactness etc. for propositional case   *)
loadt "Logic/canon.ml";;        (* First order case via canonical models     *)
loadt "Logic/herbrand.ml";;     (* Refinement to ground terms                *)
loadt "Logic/fole.ml";;         (* First order logic with equality           *)

(* ------------------------------------------------------------------------- *)
(* Completeness of resolution.                                               *)
(* ------------------------------------------------------------------------- *)

loadt "Logic/unif.ml";;         (* Unification algorithms and MGUs           *)
loadt "Logic/resolution.ml";;   (* Completeness of resolution                *)
loadt "Logic/given.ml";;        (* More refined analysis of subsumption etc. *)
loadt "Logic/linear.ml";;       (* Linear refinements                        *)
loadt "Logic/support.ml";;      (* Set-of-support tautology-free versions    *)
loadt "Logic/positive.ml";;     (* Positive and general semantic resolution  *)
loadt "Logic/givensem.ml";;     (* Adaptation of given.ml to semantic case   *)

(* ------------------------------------------------------------------------- *)
(* Prolog-style backchaining (SLD resolution).                               *)
(* ------------------------------------------------------------------------- *)

loadt "Logic/prolog.ml";;       (* Backchaining for Horn clauses             *)

(* ------------------------------------------------------------------------- *)
(* Equational logic.                                                         *)
(* ------------------------------------------------------------------------- *)

loadt "Logic/birkhoff.ml";;     (* Birkhoff's completeness theorem           *)
loadt "Logic/trs.ml";;          (* Results on simplifying convergent TRS     *)
loadt "Logic/lpo.ml";;          (* The lexicographic path ordering           *)
