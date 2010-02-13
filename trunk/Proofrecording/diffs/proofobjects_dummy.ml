(* ========================================================================= *)
(*                 Proof-objects for HOL-light                               *)
(*                                                                           *)
(*       Steven Obua, TU München, December 2004                              *)
(*                                                                           *)
(*       based on Sebastian Skalberg's HOL4 proof-objects                    *)
(*                                                                           *)
(*       dummy proof objects, is used when proof objects are switched off,   *)
(*       the real thing can be found in proofobjects_trt.ml                  *)
(* ========================================================================= *)

module type Proofobject_primitives =
  sig

    type proof

    val proof_REFL : term -> proof
    val proof_TRANS : proof * proof -> proof
    val proof_MK_COMB : proof * proof -> proof
    val proof_ASSUME : term -> proof
    val proof_EQ_MP : proof -> proof -> proof
    val proof_IMPAS : proof -> proof -> proof
    val proof_DISCH : proof -> term -> proof
    val proof_DEDUCT_ANTISYM_RULE : proof * term -> proof * term -> proof
    val proof_BETA : term -> proof
    val proof_ABS : term -> proof -> proof
    val proof_INST_TYPE : (hol_type * hol_type) list -> proof -> proof
    val proof_INST : (term * term) list -> proof -> proof
    val proof_new_definition : string -> term -> proof
    val proof_CONJ : proof -> proof -> proof
    val proof_CONJUNCT1 : proof -> proof
    val proof_CONJUNCT2 : proof -> proof
    val proof_new_basic_type_definition :
        string -> string * string -> term * term -> proof -> proof
    val proof_SPEC : term -> proof -> proof
    val proof_SYM : proof -> proof
    val proof_GEN : proof -> term -> proof
    val proof_DISJ1 : proof -> term -> proof
    val proof_DISJ2 : proof -> term -> proof
    val proof_NOTI : proof -> proof
    val proof_NOTE : proof -> proof
    val proof_CONTR : proof -> term -> proof
    val proof_DISJCASES : proof -> proof -> proof -> proof
    val proof_CHOOSE : term -> proof -> proof -> proof
    val proof_EXISTS : term -> term -> proof -> proof

    val new_axiom_name : string -> string
    val proof_new_axiom : string -> term -> proof

    val save_proof : string -> proof -> (term option) -> unit
    val proof_database : unit -> ((string * proof * (term option)) list)

    val export_proofs : string option -> (string * proof * (term option)) list -> unit
    val export_saved_proofs : string option -> unit

end;;

module Proofobjects : Proofobject_primitives = struct

  type proof = unit -> unit

  let dummy () x = x;;

  let proof_REFL _ = dummy ()
  let proof_TRANS _ = dummy ()
  let proof_MK_COMB _ = dummy ()
  let proof_ASSUME _ = dummy ()
  let proof_EQ_MP _ _ = dummy ()
  let proof_IMPAS _ _ = dummy ()
  let proof_DISCH _ _ = dummy ()
  let proof_DEDUCT_ANTISYM_RULE _ _ = dummy ()
  let proof_BETA _ = dummy ()
  let proof_ABS _ _ = dummy ()
  let proof_INST_TYPE _ _ = dummy ()
  let proof_INST _ _ = dummy ()
  let proof_new_definition _ _ = dummy ()
  let proof_CONJ _ _ = dummy ()
  let proof_CONJUNCT1 _ = dummy ()
  let proof_CONJUNCT2 _ = dummy ()
  let proof_new_basic_type_definition _ _ _ _ = dummy ()
  let proof_SPEC _ _ = dummy ()
  let proof_SYM _ = dummy ()
  let proof_GEN _ _ = dummy ()
  let proof_DISJ1 _ _ = dummy ()
  let proof_DISJ2 _ _ = dummy ()
  let proof_NOTI _ = dummy ()
  let proof_NOTE _ = dummy ()
  let proof_CONTR _ _ = dummy ()
  let proof_DISJCASES _ _ _ = dummy ()
  let proof_CHOOSE _ _ _ = dummy ()
  let proof_EXISTS _ _ _ = dummy ()
  let new_axiom_name _ = ""
  let proof_new_axiom _ _ = dummy ()
  let save_proof _ _ _ = ()
  let proof_database _ = []
  let export_proofs _ _ = ()
  let export_saved_proofs _ = ()

end;;

include Proofobjects;;
