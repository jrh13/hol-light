(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* ========================================================================= *)

module Resolution = struct

open Useful;;

(* ------------------------------------------------------------------------- *)
(* A type of resolution proof procedures.                                    *)
(* ------------------------------------------------------------------------- *)

type parameters = Parameters of {
  activeP : Active.parameters;
  waitingP : Waiting.parameters
};;

type resolution = Resolution of {
  parameters : parameters;
  active : Active.active;
  waiting : Waiting.waiting
};;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let default = Parameters {
  activeP = Active.default;
  waitingP = Waiting.default
};;

let newResolution parameters ths =
  let {activeP = activeParm; waitingP = waitingParm} = parameters in
  let (active,cls) = Active.newActive activeParm ths (* cls = factored ths *) in
  let waiting = Waiting.newWaiting waitingParm cls in
  Resolution {parameters = parameters; active = active; waiting = waiting};;

let active (Resolution {active = a}) = a;;

let waiting (Resolution {waiting = w}) = w;;

(* ------------------------------------------------------------------------- *)
(* The main proof loop.                                                      *)
(* ------------------------------------------------------------------------- *)

type decision =
  | Contradiction of Thm.thm
  | Satisfiable of Thm.thm list;;

type state =
  | Decided of decision
  | Undecided of resolution;;

let iterate res =
  let Resolution {parameters; active; waiting} = res in
  match Waiting.remove waiting with
  | None ->
      let sat = Satisfiable (List.map Clause.thm (Active.saturation active)) in
      Decided sat
  | Some ((d,cl),waiting) ->
      if Clause.isContradiction cl then
        Decided (Contradiction (Clause.thm cl))
      else
        let (active,cls) = Active.add active cl in
        let waiting = Waiting.add waiting (d,cls) in
        let res =
          Resolution {
            parameters = parameters;
            active = active;
            waiting = waiting} in
        Undecided res
;;

let rec loop res =
  match iterate res with
  | Decided dec -> dec
  | Undecided res -> loop res;;
end (* struct Resolution *)
