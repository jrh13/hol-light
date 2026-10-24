(* ========================================================================= *)
(* 4CT/redpart.ml                                                            *)
(*                                                                           *)
(* redpart.v: the reducibility check for parts.  redpart qt p holds when     *)
(* every second neighbourhood fitting the part p contains a configuration of *)
(* the quiz tree qt.  The search navigates the part with a zipper (a zpart:  *)
(* a location, the left sector reversed and the right sector), matches the   *)
(* quiz questions against the tops of the arity ranges (fitqzp) and recurses *)
(* (red_rec) on the parts obtained by popping a matched range.  Only         *)
(* soundness is proved: NO_FIT_REDPART (Coq no_fit_redpart).                 *)
(*                                                                           *)
(* The Coq section variables are explicit arguments: qt (the quiz tree),     *)
(* ahub : qarity (the hub size), red_rec : part -> bool (the recursive       *)
(* call), p0l and p0r : part (the reversed and the original part), and for   *)
(* the semantic lemmas the hypermap G and the hub dart x0.  zshiftl, zshiftr *)
(* and the zstep functions take p0l p0r first; fitqzp and red_popqzp recurse *)
(* on the question with the zpart as trailing argument.                      *)
(* ========================================================================= *)

needs "4CT/quiztree.ml";;

let zpart_loc_INDUCT,zpart_loc_RECURSION = define_type
  "zpart_loc = Znil | Zhub | Zhubl | Zhubr | Zhat | Zhatl | Zhatr
             | Zfan0l | Zfan1l | Zfan2l | Zfan3l | Zfan0r | Zfan1r | Zfan2r \
              | Zfan3r";;

let zpart_INDUCT,
  zpart_RECURSION = define_type "zpart = Zpart zpart_loc part part";;

let zp_zi = new_recursive_definition zpart_RECURSION
  `zp_zi (Zpart zi pl pr) = zi`;;
let zp_pl = new_recursive_definition zpart_RECURSION
  `zp_pl (Zpart zi pl pr) = pl`;;
let zp_pr = new_recursive_definition zpart_RECURSION
  `zp_pr (Zpart zi pl pr) = pr`;;

let zproper = new_recursive_definition zpart_RECURSION
 `zproper (Zpart zi pl pr) <=> ~(zi = Znil)`;;

let zvalid = new_definition
 `zvalid p0r pl pr <=> catrev_part pl pr = cat_part p0r p0r`;;

let zpvalid = new_recursive_definition zpart_RECURSION
 `zpvalid p0r (Zpart zi pl pr) <=> zvalid p0r pl pr`;;

(* The dart indexed by a location, from the reference hub dart x.            *)
let zmove = new_recursive_definition zpart_loc_RECURSION
 `(zmove Znil (G:(A)hypermap) x = x) /\
  (zmove Zhub G x = x) /\
  (zmove Zhubl G x = node_map G x) /\
  (zmove Zhubr G x = node_map G (node_map G x)) /\
  (zmove Zhat G x = node_map G (edge_map G (node_map G (node_map G x)))) /\
  (zmove Zhatl G x = edge_map G (node_map G (node_map G x))) /\
  (zmove Zhatr G x = face_map G (node_map G (node_map G x))) /\
  (zmove Zfan0l G x =
  face_map G (edge_map G (ITER 2 (edge_map G o node_map G) (node_map G x)))) /\
  (zmove Zfan1l G x =
  face_map G (edge_map G (ITER 3 (edge_map G o node_map G) (node_map G x)))) /\
  (zmove Zfan2l G x =
  face_map G (edge_map G (ITER 4 (edge_map G o node_map G) (node_map G x)))) /\
  (zmove Zfan3l G x =
  face_map G (edge_map G (ITER 5 (edge_map G o node_map G) (node_map G x)))) /\
  (zmove Zfan0r G x = edge_map G (ITER 2 (face_map G) (node_map G x))) /\
  (zmove Zfan1r G x = edge_map G (ITER 3 (face_map G) (node_map G x))) /\
  (zmove Zfan2r G x = edge_map G (ITER 4 (face_map G) (node_map G x))) /\
  (zmove Zfan3r G x = edge_map G (ITER 5 (face_map G) (node_map G x)))`;;

let zorg = new_definition
 `zorg (G:(A)hypermap) x0 pl = ITER (size_part pl) (face_map G) x0`;;

let zporg = new_recursive_definition zpart_RECURSION
 `zporg (G:(A)hypermap) x0 (Zpart zi pl pr) = zorg G x0 pl`;;

let zdart = new_recursive_definition zpart_RECURSION
 `zdart (G:(A)hypermap) x0 (Zpart zi pl pr) = zmove zi G (zorg G x0 pl)`;;

let zpfit = new_definition
 `zpfit (G:(A)hypermap) x0 x zp <=> zproper zp ==> zdart G x0 zp = x`;;

let hub_range = new_recursive_definition qarity_RECURSION
 `(hub_range Qa5 = Pr55) /\ (hub_range Qa6 = Pr66) /\ (hub_range Qa7 = Pr77) /\
  (hub_range Qa8 = Pr88) /\ (hub_range Qa9 = Pr99) /\
  (hub_range Qa10 = Pr99) /\
  (hub_range Qa11 = Pr99)`;;

let zrange_loc = new_recursive_definition zpart_loc_RECURSION
 `(zrange_loc ahub Znil pl pr = Pr59) /\
  (zrange_loc ahub Zhub pl pr = hub_range ahub) /\
  (zrange_loc ahub Zhubl pl pr = get_spoke pl) /\
  (zrange_loc ahub Zhubr pl pr = get_spoke pr) /\
  (zrange_loc ahub Zhat pl pr = get_hat pr) /\
  (zrange_loc ahub Zhatl pl pr = get_spoke pl) /\
  (zrange_loc ahub Zhatr pl pr = get_spoke pr) /\
  (zrange_loc ahub Zfan0l pl pr = get_hat pr) /\
  (zrange_loc ahub Zfan1l pl pr = get_fan1l pl) /\
  (zrange_loc ahub Zfan2l pl pr = get_fan2l pl) /\
  (zrange_loc ahub Zfan3l pl pr = get_fan3l pl) /\
  (zrange_loc ahub Zfan0r pl pr = get_hat pl) /\
  (zrange_loc ahub Zfan1r pl pr = get_fan1r pl) /\
  (zrange_loc ahub Zfan2r pl pr = get_fan2r pl) /\
  (zrange_loc ahub Zfan3r pl pr = get_fan3r pl)`;;

let zrange = new_recursive_definition zpart_RECURSION
 `zrange ahub (Zpart zi pl pr) = zrange_loc ahub zi pl pr`;;

let shift_part = new_definition
 `shift_part p1 p2 = cat_part (take_part 1 p1) p2`;;

(* zshiftl: location zi in the subpart to the left (wrapping to p0l/p0r).    *)
let zshiftl_aux = new_recursive_definition part_RECURSION
 `(zshiftl_aux p0l p0r zi Pnil pr =
  Zpart zi (drop_part 1 p0l) (shift_part p0l p0r)) /\
  (zshiftl_aux p0l p0r zi (Pcons s h pl) pr =
     (if pl = Pnil then Zpart zi p0l p0r else Zpart zi pl (Pcons s h pr))) /\
  (zshiftl_aux p0l p0r zi (Pcons6 h f1 pl) pr =
     (if pl = Pnil then Zpart zi p0l p0r else Zpart zi pl (Pcons6 h f1 pr))) /\
  (zshiftl_aux p0l p0r zi (Pcons7 h f1 f2 pl) pr =
     (if pl = Pnil then Zpart zi p0l p0r else Zpart zi pl (Pcons7 h f1 f2 pr)))
     /\
  (zshiftl_aux p0l p0r zi (Pcons8 h f1 f2 f3 pl) pr =
     (if pl = Pnil then Zpart zi p0l p0r
     else Zpart zi pl (Pcons8 h f1 f2 f3 pr)))`;;

let zshiftl = new_recursive_definition zpart_RECURSION
 `zshiftl p0l p0r zi (Zpart zi0 pl pr) = zshiftl_aux p0l p0r zi pl pr`;;

let zshiftr_aux = new_recursive_definition part_RECURSION
 `(zshiftr_aux p0l p0r zi pl Pnil =
  Zpart zi (shift_part p0r p0l) (drop_part 1 p0r)) /\
  (zshiftr_aux p0l p0r zi pl (Pcons s h pr) =
     (if pr = Pnil then Zpart zi p0l p0r else Zpart zi (Pcons s h pl) pr)) /\
  (zshiftr_aux p0l p0r zi pl (Pcons6 h f1 pr) =
     (if pr = Pnil then Zpart zi p0l p0r else Zpart zi (Pcons6 h f1 pl) pr)) /\
  (zshiftr_aux p0l p0r zi pl (Pcons7 h f1 f2 pr) =
     (if pr = Pnil then Zpart zi p0l p0r else Zpart zi (Pcons7 h f1 f2 pl) pr))
     /\
  (zshiftr_aux p0l p0r zi pl (Pcons8 h f1 f2 f3 pr) =
     (if pr = Pnil then Zpart zi p0l p0r
     else Zpart zi (Pcons8 h f1 f2 f3 pl) pr))`;;

let zshiftr = new_recursive_definition zpart_RECURSION
 `zshiftr p0l p0r zi (Zpart zi0 pl pr) = zshiftr_aux p0l p0r zi pl pr`;;

let zfanL = new_recursive_definition part_RECURSION
 `(zfanL Pnil = Znil) /\
  (zfanL (Pcons s h p) = (if s = Pr55 then Zfan0l else Znil)) /\
  (zfanL (Pcons6 h f1 p) = Zfan1l) /\
  (zfanL (Pcons7 h f1 f2 p) = Zfan2l) /\
  (zfanL (Pcons8 h f1 f2 f3 p) = Zfan3l)`;;

let zfanR = new_recursive_definition part_RECURSION
 `(zfanR Pnil = Znil) /\
  (zfanR (Pcons s h p) = (if s = Pr55 then Zfan0r else Znil)) /\
  (zfanR (Pcons6 h f1 p) = Zfan1r) /\
  (zfanR (Pcons7 h f1 f2 p) = Zfan2r) /\
  (zfanR (Pcons8 h f1 f2 f3 p) = Zfan3r)`;;

let zfanLt = new_recursive_definition part_RECURSION
 `(zfanLt Pnil = Znil) /\
  (zfanLt (Pcons s h p) =
     (if s = Pr55 then Zfan0l else if s = Pr56 \/ s = Pr66 then Zfan1l
     else Znil)) /\
  (zfanLt (Pcons6 h f1 p) = Zfan1l) /\
  (zfanLt (Pcons7 h f1 f2 p) = Zfan2l) /\
  (zfanLt (Pcons8 h f1 f2 f3 p) = Zfan3l)`;;

let zfanRt = new_recursive_definition part_RECURSION
 `(zfanRt Pnil = Znil) /\
  (zfanRt (Pcons s h p) =
     (if s = Pr55 then Zfan0r else if s = Pr56 \/ s = Pr66 then Zfan1r
     else Znil)) /\
  (zfanRt (Pcons6 h f1 p) = Zfan1r) /\
  (zfanRt (Pcons7 h f1 f2 p) = Zfan2r) /\
  (zfanRt (Pcons8 h f1 f2 f3 p) = Zfan3r)`;;

(* The step functions: zstep[LR] zp fits qstep[LR] (zdart zp).               *)
let zstepL_loc = new_recursive_definition zpart_loc_RECURSION
 `(zstepL_loc p0l p0r Znil pl pr = Zpart Znil pl pr) /\
  (zstepL_loc p0l p0r Zhub pl pr = zshiftl p0l p0r Zhubl (Zpart Zhub pl pr)) /\
  (zstepL_loc p0l p0r Zhubl pl pr = Zpart Zhat pl pr) /\
  (zstepL_loc p0l p0r Zhubr pl pr = zshiftr p0l p0r Zhubr (Zpart Zhubr pl pr))
  /\
  (zstepL_loc p0l p0r Zhat pl pr =
  zshiftr p0l p0r (zfanL pr) (Zpart Zhat pl pr)) /\
  (zstepL_loc p0l p0r Zhatl pl pr = Zpart (zfanR pl) pl pr) /\
  (zstepL_loc p0l p0r Zhatr pl pr = Zpart Zhub pl pr) /\
  (zstepL_loc p0l p0r Zfan0l pl pr = Zpart Zhatr pl pr) /\
  (zstepL_loc p0l p0r Zfan1l pl pr = Zpart Zfan0l pl pr) /\
  (zstepL_loc p0l p0r Zfan2l pl pr = Zpart Zfan1l pl pr) /\
  (zstepL_loc p0l p0r Zfan3l pl pr = Zpart Zfan2l pl pr) /\
  (zstepL_loc p0l p0r Zfan0r pl pr = Zpart Znil pl pr) /\
  (zstepL_loc p0l p0r Zfan1r pl pr = Zpart Znil pl pr) /\
  (zstepL_loc p0l p0r Zfan2r pl pr = Zpart Znil pl pr) /\
  (zstepL_loc p0l p0r Zfan3r pl pr = Zpart Znil pl pr)`;;

let zstepL = new_recursive_definition zpart_RECURSION
 `zstepL p0l p0r (Zpart zi pl pr) = zstepL_loc p0l p0r zi pl pr`;;

let zstepR_loc = new_recursive_definition zpart_loc_RECURSION
 `(zstepR_loc p0l p0r Znil pl pr = Zpart Znil pl pr) /\
  (zstepR_loc p0l p0r Zhub pl pr = zshiftr p0l p0r Zhubr (Zpart Zhub pl pr)) /\
  (zstepR_loc p0l p0r Zhubl pl pr = zshiftl p0l p0r Zhubl (Zpart Zhubl pl pr))
  /\
  (zstepR_loc p0l p0r Zhubr pl pr = Zpart Zhat pl pr) /\
  (zstepR_loc p0l p0r Zhat pl pr = Zpart (zfanR pl) pl pr) /\
  (zstepR_loc p0l p0r Zhatl pl pr = Zpart Zhub pl pr) /\
  (zstepR_loc p0l p0r Zhatr pl pr =
  zshiftr p0l p0r (zfanL pr) (Zpart Zhatr pl pr)) /\
  (zstepR_loc p0l p0r Zfan0l pl pr = Zpart Znil pl pr) /\
  (zstepR_loc p0l p0r Zfan1l pl pr = Zpart Znil pl pr) /\
  (zstepR_loc p0l p0r Zfan2l pl pr = Zpart Znil pl pr) /\
  (zstepR_loc p0l p0r Zfan3l pl pr = Zpart Znil pl pr) /\
  (zstepR_loc p0l p0r Zfan0r pl pr =
  zshiftl p0l p0r Zhatl (Zpart Zfan0r pl pr)) /\
  (zstepR_loc p0l p0r Zfan1r pl pr = Zpart Zfan0r pl pr) /\
  (zstepR_loc p0l p0r Zfan2r pl pr = Zpart Zfan1r pl pr) /\
  (zstepR_loc p0l p0r Zfan3r pl pr = Zpart Zfan2r pl pr)`;;

let zstepR = new_recursive_definition zpart_RECURSION
 `zstepR p0l p0r (Zpart zi pl pr) = zstepR_loc p0l p0r zi pl pr`;;

(* t variants (assume zpfit_top): only the Zhatl / Zhatr cases differ.       *)
let zstepLt_loc = new_recursive_definition zpart_loc_RECURSION
 `(zstepLt_loc p0l p0r Znil pl pr = Zpart Znil pl pr) /\
  (zstepLt_loc p0l p0r Zhub pl pr = zshiftl p0l p0r Zhubl (Zpart Zhub pl pr))
  /\
  (zstepLt_loc p0l p0r Zhubl pl pr = Zpart Zhat pl pr) /\
  (zstepLt_loc p0l p0r Zhubr pl pr = zshiftr p0l p0r Zhubr (Zpart Zhubr pl pr))
  /\
  (zstepLt_loc p0l p0r Zhat pl pr =
  zshiftr p0l p0r (zfanL pr) (Zpart Zhat pl pr)) /\
  (zstepLt_loc p0l p0r Zhatl pl pr = Zpart (zfanRt pl) pl pr) /\
  (zstepLt_loc p0l p0r Zhatr pl pr = Zpart Zhub pl pr) /\
  (zstepLt_loc p0l p0r Zfan0l pl pr = Zpart Zhatr pl pr) /\
  (zstepLt_loc p0l p0r Zfan1l pl pr = Zpart Zfan0l pl pr) /\
  (zstepLt_loc p0l p0r Zfan2l pl pr = Zpart Zfan1l pl pr) /\
  (zstepLt_loc p0l p0r Zfan3l pl pr = Zpart Zfan2l pl pr) /\
  (zstepLt_loc p0l p0r Zfan0r pl pr = Zpart Znil pl pr) /\
  (zstepLt_loc p0l p0r Zfan1r pl pr = Zpart Znil pl pr) /\
  (zstepLt_loc p0l p0r Zfan2r pl pr = Zpart Znil pl pr) /\
  (zstepLt_loc p0l p0r Zfan3r pl pr = Zpart Znil pl pr)`;;

let zstepLt = new_recursive_definition zpart_RECURSION
 `zstepLt p0l p0r (Zpart zi pl pr) = zstepLt_loc p0l p0r zi pl pr`;;

let zstepRt_loc = new_recursive_definition zpart_loc_RECURSION
 `(zstepRt_loc p0l p0r Znil pl pr = Zpart Znil pl pr) /\
  (zstepRt_loc p0l p0r Zhub pl pr = zshiftr p0l p0r Zhubr (Zpart Zhub pl pr))
  /\
  (zstepRt_loc p0l p0r Zhubl pl pr = zshiftl p0l p0r Zhubl (Zpart Zhubl pl pr))
  /\
  (zstepRt_loc p0l p0r Zhubr pl pr = Zpart Zhat pl pr) /\
  (zstepRt_loc p0l p0r Zhat pl pr = Zpart (zfanR pl) pl pr) /\
  (zstepRt_loc p0l p0r Zhatl pl pr = Zpart Zhub pl pr) /\
  (zstepRt_loc p0l p0r Zhatr pl pr =
  zshiftr p0l p0r (zfanLt pr) (Zpart Zhatr pl pr)) /\
  (zstepRt_loc p0l p0r Zfan0l pl pr = Zpart Znil pl pr) /\
  (zstepRt_loc p0l p0r Zfan1l pl pr = Zpart Znil pl pr) /\
  (zstepRt_loc p0l p0r Zfan2l pl pr = Zpart Znil pl pr) /\
  (zstepRt_loc p0l p0r Zfan3l pl pr = Zpart Znil pl pr) /\
  (zstepRt_loc p0l p0r Zfan0r pl pr =
  zshiftl p0l p0r Zhatl (Zpart Zfan0r pl pr)) /\
  (zstepRt_loc p0l p0r Zfan1r pl pr = Zpart Zfan0r pl pr) /\
  (zstepRt_loc p0l p0r Zfan2r pl pr = Zpart Zfan1r pl pr) /\
  (zstepRt_loc p0l p0r Zfan3r pl pr = Zpart Zfan2r pl pr)`;;

let zstepRt = new_recursive_definition zpart_RECURSION
 `zstepRt p0l p0r (Zpart zi pl pr) = zstepRt_loc p0l p0r zi pl pr`;;

(* Top qarity of a range; fitting / popping a range.                         *)
let topqa = new_recursive_definition prange_RECURSION
 `(topqa Pr55 = Qa5) /\ (topqa Pr66 = Qa6) /\ (topqa Pr77 = Qa7) /\
  (topqa Pr88 = Qa8) /\
  (topqa Pr99 = Qa9) /\ (topqa Pr56 = Qa6) /\ (topqa Pr67 = Qa7) /\
  (topqa Pr78 = Qa8) /\
  (topqa Pr89 = Qa9) /\ (topqa Pr57 = Qa7) /\ (topqa Pr68 = Qa8) /\
  (topqa Pr79 = Qa9) /\
  (topqa Pr58 = Qa8) /\ (topqa Pr69 = Qa9) /\ (topqa Pr59 = Qa9)`;;

(* Coq's table; equals (qa <= 8) && (qa == topqa r) (lemma fitqa_topqa).     *)
let fitqa = new_definition
 `fitqa r qa <=> nat_of_qarity qa <= 8 /\ qa = topqa r`;;

let popqa = new_recursive_definition prange_RECURSION
 `(popqa Pr55 = Pr99) /\ (popqa Pr66 = Pr99) /\ (popqa Pr77 = Pr99) /\
  (popqa Pr88 = Pr99) /\
  (popqa Pr99 = Pr99) /\ (popqa Pr56 = Pr55) /\ (popqa Pr67 = Pr66) /\
  (popqa Pr78 = Pr77) /\
  (popqa Pr89 = Pr99) /\ (popqa Pr57 = Pr56) /\ (popqa Pr68 = Pr67) /\
  (popqa Pr79 = Pr99) /\
  (popqa Pr58 = Pr57) /\ (popqa Pr69 = Pr99) /\ (popqa Pr59 = Pr99)`;;

let zpfit_top = new_definition
 `zpfit_top (G:(A)hypermap) x0 ahub zp <=>
    arity G (zdart G x0 zp) = nat_of_qarity (topqa (zrange ahub zp))`;;

(* ------------------------------------------------------------------------- *)
(* Popping a range and recursing.                                            *)
(* ------------------------------------------------------------------------- *)

let red_pcons = new_definition
 `red_pcons (red_rec:part->bool) nhub p0r (pc:prange->part->part) r pr =
    let rpc = \r'. red_rec (take_part nhub (cat_part (pc r' pr) p0r)) in
    if r = Pr56 then rpc Pr55 else if r = Pr57 then rpc Pr56 else
    if r = Pr58 then rpc Pr57 else if r = Pr67 then rpc Pr66 else
    if r = Pr68 then rpc Pr67 else if r = Pr78 then rpc Pr77 else T`;;

let red_popr_spoke = new_recursive_definition part_RECURSION
 `(red_popr_spoke (red_rec:part->bool) nhub p0r Pnil = T) /\
  (red_popr_spoke red_rec nhub p0r (Pcons s h p) =
  red_pcons red_rec nhub p0r (\r'. Pcons r' h) s p) /\
  (red_popr_spoke red_rec nhub p0r (Pcons6 h f1 p) = T) /\
  (red_popr_spoke red_rec nhub p0r (Pcons7 h f1 f2 p) = T) /\
  (red_popr_spoke red_rec nhub p0r (Pcons8 h f1 f2 f3 p) = T)`;;

let red_popr_hat = new_recursive_definition part_RECURSION
 `(red_popr_hat (red_rec:part->bool) nhub p0r Pnil = T) /\
  (red_popr_hat red_rec nhub p0r (Pcons s h p) =
  red_pcons red_rec nhub p0r (\r'. Pcons s r') h p) /\
  (red_popr_hat red_rec nhub p0r (Pcons6 h f1 p) =
  red_pcons red_rec nhub p0r (\r'. Pcons6 r' f1) h p) /\
  (red_popr_hat red_rec nhub p0r (Pcons7 h f1 f2 p) =
  red_pcons red_rec nhub p0r (\r'. Pcons7 r' f1 f2) h p) /\
  (red_popr_hat red_rec nhub p0r (Pcons8 h f1 f2 f3 p) =
  red_pcons red_rec nhub p0r (\r'. Pcons8 r' f1 f2 f3) h p)`;;

let red_popl_spoke = new_recursive_definition part_RECURSION
 `(red_popl_spoke (red_rec:part->bool) nhub p0r Pnil pr = T) /\
  (red_popl_spoke red_rec nhub p0r (Pcons s h p) pr =
  red_pcons red_rec nhub p0r (\r'. Pcons r' h) s pr) /\
  (red_popl_spoke red_rec nhub p0r (Pcons6 h f1 p) pr = T) /\
  (red_popl_spoke red_rec nhub p0r (Pcons7 h f1 f2 p) pr = T) /\
  (red_popl_spoke red_rec nhub p0r (Pcons8 h f1 f2 f3 p) pr = T)`;;

let red_popl_hat = new_recursive_definition part_RECURSION
 `(red_popl_hat (red_rec:part->bool) nhub p0r Pnil pr = T) /\
  (red_popl_hat red_rec nhub p0r (Pcons s h p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons s r) h pr) /\
  (red_popl_hat red_rec nhub p0r (Pcons6 h f1 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons6 r f1) h pr) /\
  (red_popl_hat red_rec nhub p0r (Pcons7 h f1 f2 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons7 r f1 f2) h pr) /\
  (red_popl_hat red_rec nhub p0r (Pcons8 h f1 f2 f3 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons8 r f1 f2 f3) h pr)`;;

let red_popl_fan1l = new_recursive_definition part_RECURSION
 `(red_popl_fan1l (red_rec:part->bool) nhub p0r Pnil pr = T) /\
  (red_popl_fan1l red_rec nhub p0r (Pcons s h p) pr = T) /\
  (red_popl_fan1l red_rec nhub p0r (Pcons6 h f1 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons6 h r) f1 pr) /\
  (red_popl_fan1l red_rec nhub p0r (Pcons7 h f1 f2 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons7 h f1 r) f2 pr) /\
  (red_popl_fan1l red_rec nhub p0r (Pcons8 h f1 f2 f3 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons8 h f1 f2 r) f3 pr)`;;

let red_popl_fan2l = new_recursive_definition part_RECURSION
 `(red_popl_fan2l (red_rec:part->bool) nhub p0r Pnil pr = T) /\
  (red_popl_fan2l red_rec nhub p0r (Pcons s h p) pr = T) /\
  (red_popl_fan2l red_rec nhub p0r (Pcons6 h f1 p) pr = T) /\
  (red_popl_fan2l red_rec nhub p0r (Pcons7 h f1 f2 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons7 h r f2) f1 pr) /\
  (red_popl_fan2l red_rec nhub p0r (Pcons8 h f1 f2 f3 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons8 h f1 r f3) f2 pr)`;;

let red_popl_fan3l = new_recursive_definition part_RECURSION
 `(red_popl_fan3l (red_rec:part->bool) nhub p0r Pnil pr = T) /\
  (red_popl_fan3l red_rec nhub p0r (Pcons s h p) pr = T) /\
  (red_popl_fan3l red_rec nhub p0r (Pcons6 h f1 p) pr = T) /\
  (red_popl_fan3l red_rec nhub p0r (Pcons7 h f1 f2 p) pr = T) /\
  (red_popl_fan3l red_rec nhub p0r (Pcons8 h f1 f2 f3 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons8 h r f2 f3) f1 pr)`;;

let red_popl_fan1r = new_recursive_definition part_RECURSION
 `(red_popl_fan1r (red_rec:part->bool) nhub p0r Pnil pr = T) /\
  (red_popl_fan1r red_rec nhub p0r (Pcons s h p) pr = T) /\
  (red_popl_fan1r red_rec nhub p0r (Pcons6 h f1 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons6 h r) f1 pr) /\
  (red_popl_fan1r red_rec nhub p0r (Pcons7 h f1 f2 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons7 h r f2) f1 pr) /\
  (red_popl_fan1r red_rec nhub p0r (Pcons8 h f1 f2 f3 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons8 h r f2 f3) f1 pr)`;;

let red_popl_fan2r = new_recursive_definition part_RECURSION
 `(red_popl_fan2r (red_rec:part->bool) nhub p0r Pnil pr = T) /\
  (red_popl_fan2r red_rec nhub p0r (Pcons s h p) pr = T) /\
  (red_popl_fan2r red_rec nhub p0r (Pcons6 h f1 p) pr = T) /\
  (red_popl_fan2r red_rec nhub p0r (Pcons7 h f1 f2 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons7 h f1 r) f2 pr) /\
  (red_popl_fan2r red_rec nhub p0r (Pcons8 h f1 f2 f3 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons8 h f1 r f3) f2 pr)`;;

let red_popl_fan3r = new_recursive_definition part_RECURSION
 `(red_popl_fan3r (red_rec:part->bool) nhub p0r Pnil pr = T) /\
  (red_popl_fan3r red_rec nhub p0r (Pcons s h p) pr = T) /\
  (red_popl_fan3r red_rec nhub p0r (Pcons6 h f1 p) pr = T) /\
  (red_popl_fan3r red_rec nhub p0r (Pcons7 h f1 f2 p) pr = T) /\
  (red_popl_fan3r red_rec nhub p0r (Pcons8 h f1 f2 f3 p) pr =
  red_pcons red_rec nhub p0r (\r. Pcons8 h f1 f2 r) f3 pr)`;;

let red_pop_loc = new_recursive_definition zpart_loc_RECURSION
 `(red_pop_loc (red_rec:part->bool) nhub p0r Znil pl pr = T) /\
  (red_pop_loc red_rec nhub p0r Zhub pl pr = T) /\
  (red_pop_loc red_rec nhub p0r Zhubl pl pr =
  red_popl_spoke red_rec nhub p0r pl pr) /\
  (red_pop_loc red_rec nhub p0r Zhubr pl pr =
  red_popr_spoke red_rec nhub p0r pr) /\
  (red_pop_loc red_rec nhub p0r Zhat pl pr = red_popr_hat red_rec nhub p0r pr)
  /\
  (red_pop_loc red_rec nhub p0r Zhatl pl pr =
  red_popl_spoke red_rec nhub p0r pl pr) /\
  (red_pop_loc red_rec nhub p0r Zhatr pl pr =
  red_popr_spoke red_rec nhub p0r pr) /\
  (red_pop_loc red_rec nhub p0r Zfan0l pl pr =
  red_popr_hat red_rec nhub p0r pr) /\
  (red_pop_loc red_rec nhub p0r Zfan1l pl pr =
  red_popl_fan1l red_rec nhub p0r pl pr) /\
  (red_pop_loc red_rec nhub p0r Zfan2l pl pr =
  red_popl_fan2l red_rec nhub p0r pl pr) /\
  (red_pop_loc red_rec nhub p0r Zfan3l pl pr =
  red_popl_fan3l red_rec nhub p0r pl pr) /\
  (red_pop_loc red_rec nhub p0r Zfan0r pl pr =
  red_popl_hat red_rec nhub p0r pl pr) /\
  (red_pop_loc red_rec nhub p0r Zfan1r pl pr =
  red_popl_fan1r red_rec nhub p0r pl pr) /\
  (red_pop_loc red_rec nhub p0r Zfan2r pl pr =
  red_popl_fan2r red_rec nhub p0r pl pr) /\
  (red_pop_loc red_rec nhub p0r Zfan3r pl pr =
  red_popl_fan3r red_rec nhub p0r pl pr)`;;

let red_pop = new_recursive_definition zpart_RECURSION
 `red_pop (red_rec:part->bool) nhub p0r (Zpart zi pl pr) =
  red_pop_loc red_rec nhub p0r zi pl pr`;;

(* fitqzp: the question's arities are the tops of the ranges along the walk. *)
let fitqzp = new_recursive_definition question_RECURSION
 `(fitqzp ahub p0l p0r Qask0 zp = T) /\
  (fitqzp ahub p0l p0r (Qask1 qa) zp = fitqa (zrange ahub zp) qa) /\
  (fitqzp ahub p0l p0r (QaskL qa ql) zp =
     (if fitqa (zrange ahub zp) qa
     then fitqzp ahub p0l p0r ql (zstepLt p0l p0r zp) else F)) /\
  (fitqzp ahub p0l p0r (QaskR qa qr) zp =
     (if fitqa (zrange ahub zp) qa
     then fitqzp ahub p0l p0r qr (zstepRt p0l p0r zp) else F)) /\
  (fitqzp ahub p0l p0r (QaskLR qa ql qr) zp =
     (if fitqa (zrange ahub zp) qa then
        (if fitqzp ahub p0l p0r ql (zstepL p0l p0r zp)
         then fitqzp ahub p0l p0r qr (zstepR p0l p0r zp) else F)
      else F)) /\
  (fitqzp ahub p0l p0r (QaskLL qa ql) zp =
     (if fitqa (zrange ahub (zstepL p0l p0r zp)) qa
      then fitqzp ahub p0l p0r ql (zstepL p0l p0r (zstepL p0l p0r zp)) else F))
      /\
  (fitqzp ahub p0l p0r (QaskRR qa qr) zp =
     (if fitqa (zrange ahub (zstepR p0l p0r zp)) qa
      then fitqzp ahub p0l p0r qr
      (zstepR p0l p0r (zstepR p0l p0r zp)) else F))`;;

let red_popqzp = new_recursive_definition question_RECURSION
 `(red_popqzp (red_rec:part->bool) nhub p0l p0r Qask0 zp = T) /\
  (red_popqzp red_rec nhub p0l p0r (Qask1 qa) zp = red_pop red_rec nhub p0r zp)
  /\
  (red_popqzp red_rec nhub p0l p0r (QaskL qa ql) zp =
     (red_pop red_rec nhub p0r zp /\
     red_popqzp red_rec nhub p0l p0r ql (zstepLt p0l p0r zp))) /\
  (red_popqzp red_rec nhub p0l p0r (QaskR qa qr) zp =
     (red_pop red_rec nhub p0r zp /\
     red_popqzp red_rec nhub p0l p0r qr (zstepRt p0l p0r zp))) /\
  (red_popqzp red_rec nhub p0l p0r (QaskLR qa ql qr) zp =
     (red_pop red_rec nhub p0r zp /\
      red_popqzp red_rec nhub p0l p0r ql (zstepL p0l p0r zp) /\
      red_popqzp red_rec nhub p0l p0r qr (zstepR p0l p0r zp))) /\
  (red_popqzp red_rec nhub p0l p0r (QaskLL qa ql) zp =
     (red_pop red_rec nhub p0r (zstepL p0l p0r zp) /\
      red_popqzp red_rec nhub p0l p0r ql (zstepL p0l p0r (zstepL p0l p0r zp))))
      /\
  (red_popqzp red_rec nhub p0l p0r (QaskRR qa qr) zp =
     (red_pop red_rec nhub p0r (zstepR p0l p0r zp) /\
      red_popqzp red_rec nhub p0l p0r qr
      (zstepR p0l p0r (zstepR p0l p0r zp))))`;;

(* red_qzt_leaf: some leaf of the 0-height tree qtl fits (fitqzp) at the     *)
(* three zparts and all popped parts are reducible.                          *)
let red_qzt_leaf = new_recursive_definition quiz_tree_RECURSION
 `(red_qzt_leaf (red_rec:part->bool) nhub ahub p0l p0r zp1 zp2 zp3 QztNil = F)
  /\
  (red_qzt_leaf red_rec nhub ahub p0l p0r zp1 zp2 zp3 (QztLeaf q1 q2 q3 qtl') =
     (if fitqzp ahub p0l p0r q3 zp3 then
        (if fitqzp ahub p0l p0r q2 zp2 then
           (if fitqzp ahub p0l p0r q1 zp1 then
              (red_popqzp red_rec nhub p0l p0r q1 zp1 /\
               red_popqzp red_rec nhub p0l p0r q2 zp2 /\
               red_popqzp red_rec nhub p0l p0r q3 zp3)
            else red_qzt_leaf red_rec nhub ahub p0l p0r zp1 zp2 zp3 qtl')
         else red_qzt_leaf red_rec nhub ahub p0l p0r zp1 zp2 zp3 qtl')
      else red_qzt_leaf red_rec nhub ahub p0l p0r zp1 zp2 zp3 qtl')) /\
  (red_qzt_leaf red_rec nhub ahub p0l p0r zp1 zp2 zp3
  (QztNode t5 t6 t7 t8) = F) /\
  (red_qzt_leaf red_rec nhub ahub p0l p0r zp1 zp2 zp3
  (QztHubNode t58 t9 t10 t11) = F)`;;

let qzt_getr = new_recursive_definition quiz_tree_RECURSION
 `(qzt_getr r QztNil = QztNil) /\
  (qzt_getr r (QztLeaf q1 q2 q3 t) = QztNil) /\
  (qzt_getr r (QztNode qt5 qt6 qt7 qt8) =
     (if r = Pr55 then qt5
      else if r = Pr56 \/ r = Pr66 then qt6
      else if r = Pr57 \/ r = Pr67 \/ r = Pr77 then qt7
      else if r = Pr58 \/ r = Pr68 \/ r = Pr78 \/ r = Pr88 then qt8
      else QztNil)) /\
  (qzt_getr r (QztHubNode t58 t9 t10 t11) = QztNil)`;;

(* The per-sector case analysis of red_zpart_rec (Coq's inner `match pr`).   *)
let red_zpart_cases = new_recursive_definition part_RECURSION
 `(red_zpart_cases (red_rec:part->bool) nhub ahub p0l p0r pl pl' pr' sqt
  Pnil = F) /\
  (red_zpart_cases red_rec nhub ahub p0l p0r pl pl' pr' sqt (Pcons s h p) =
     (if s = Pr55 then
        (if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zhatr pl' pr')
        (Zpart Zhatl pl (Pcons s h p))
              (Zpart Znil pl' pr') (qzt_getr (get_hat pr') (qzt_getr h sqt))
         then red_popr_hat red_rec nhub p0r pr' /\
         red_popr_hat red_rec nhub p0r (Pcons s h p) else F)
      else F)) /\
  (red_zpart_cases red_rec nhub ahub p0l p0r pl pl' pr' sqt (Pcons6 h f1 p) =
     (if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zfan0l pl' pr')
     (Zpart Zhatl pl (Pcons6 h f1 p))
           (Zpart Znil pl' pr') (qzt_getr f1 (qzt_getr h sqt))
      then red_popl_fan1r red_rec nhub p0r pl' pr' /\
      red_popr_hat red_rec nhub p0r (Pcons6 h f1 p)
      else if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zhatr pl' pr')
      (Zpart Zfan0r pl' pr')
                (Zpart Znil pl' pr') (qzt_getr (get_hat pr') (qzt_getr f1 sqt))
      then red_popr_hat red_rec nhub p0r pr' /\
      red_popl_fan1r red_rec nhub p0r pl' pr'
      else F)) /\
  (red_zpart_cases red_rec nhub ahub p0l p0r pl pl' pr' sqt
  (Pcons7 h f1 f2 p) =
     (if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zfan1l pl' pr')
     (Zpart Zhatl pl (Pcons7 h f1 f2 p))
           (Zpart Znil pl' pr') (qzt_getr f1 (qzt_getr h sqt))
      then red_popl_fan1r red_rec nhub p0r pl' pr' /\
      red_popr_hat red_rec nhub p0r (Pcons7 h f1 f2 p)
      else if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zfan0l pl' pr')
      (Zpart Zfan0r pl' pr')
                (Zpart Znil pl' pr') (qzt_getr f2 (qzt_getr f1 sqt))
      then red_popl_fan2r red_rec nhub p0r pl' pr' /\
      red_popl_fan1r red_rec nhub p0r pl' pr'
      else if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zhatr pl' pr')
      (Zpart Zfan1r pl' pr')
                (Zpart Znil pl' pr') (qzt_getr (get_hat pr') (qzt_getr f2 sqt))
      then red_popr_hat red_rec nhub p0r pr' /\
      red_popl_fan2r red_rec nhub p0r pl' pr'
      else F)) /\
  (red_zpart_cases red_rec nhub ahub p0l p0r pl pl' pr' sqt
  (Pcons8 h f1 f2 f3 p) =
     (if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zfan2l pl' pr')
     (Zpart Zhatl pl (Pcons8 h f1 f2 f3 p))
           (Zpart Znil pl' pr') (qzt_getr f1 (qzt_getr h sqt))
      then red_popl_fan1r red_rec nhub p0r pl' pr' /\
      red_popr_hat red_rec nhub p0r (Pcons8 h f1 f2 f3 p)
      else if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zfan1l pl' pr')
      (Zpart Zfan0r pl' pr')
                (Zpart Znil pl' pr') (qzt_getr f2 (qzt_getr f1 sqt))
      then red_popl_fan2r red_rec nhub p0r pl' pr' /\
      red_popl_fan1r red_rec nhub p0r pl' pr'
      else if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zfan0l pl' pr')
      (Zpart Zfan1r pl' pr')
                (Zpart Znil pl' pr') (qzt_getr f3 (qzt_getr f2 sqt))
      then red_popl_fan3r red_rec nhub p0r pl' pr' /\
      red_popl_fan2r red_rec nhub p0r pl' pr'
      else if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zhatr pl' pr')
      (Zpart Zfan2r pl' pr')
                (Zpart Znil pl' pr') (qzt_getr (get_hat pr') (qzt_getr f3 sqt))
      then red_popr_hat red_rec nhub p0r pr' /\
      red_popl_fan3r red_rec nhub p0r pl' pr'
      else F))`;;

(* One sector of the search, for the zpart zp (= Zpart _ pl pr) and its      *)
(* right shift zp' (= Zpart _ pl' pr').                                      *)
let red_zpart_step = new_definition
 `red_zpart_step (red_rec:part->bool) nhub ahub qt p0l p0r zp zp' =
    let pl = zp_pl zp and pr = zp_pr zp and pl' = zp_pl zp'
    and pr' = zp_pr zp' in
    let s = get_spoke pr in
    let sqt = qzt_getr s (qzt_truncate qt) in
    if qzt_proper sqt then
      (let sl = get_spoke pl in
       if red_qzt_leaf red_rec nhub ahub p0l p0r (Zpart Zhubr pl' pr')
       (zshiftl p0l p0r Zhubl zp)
            (Zpart Zhat pl pr) (qzt_getr s (qzt_getr sl (qzt_get1 ahub qt)))
       then red_popr_spoke red_rec nhub p0r pr /\
       red_popl_spoke red_rec nhub p0r pl pr
       else if red_qzt_leaf red_rec nhub ahub p0l p0r
       (Zpart (zfanLt pr) pl' pr') zp
                 (Zpart (zfanRt pl) pl pr)
                 (qzt_getr (get_hat pr) (qzt_getr sl sqt))
       then red_popr_hat red_rec nhub p0r pr /\
       red_popl_spoke red_rec nhub p0r pl pr /\
            red_popr_spoke red_rec nhub p0r pr
       else red_zpart_cases red_rec nhub ahub p0l p0r pl pl' pr' sqt pr)
    else F`;;

let red_zpart_rec = new_recursive_definition num_RECURSION
 `(red_zpart_rec (red_rec:part->bool) nhub ahub qt p0l p0r 0 zp = F) /\
  (red_zpart_rec red_rec nhub ahub qt p0l p0r (SUC d) zp =
     (if red_zpart_step red_rec nhub ahub qt p0l p0r zp
     (zshiftr p0l p0r Zhub zp) then T
      else red_zpart_rec red_rec nhub ahub qt p0l p0r d
      (zshiftr p0l p0r Zhub zp)))`;;

let red_zpart = new_definition
 `red_zpart (red_rec:part->bool) ahub qt p0l p0r =
    red_zpart_rec red_rec (nat_of_qarity ahub) ahub qt p0l p0r
    (nat_of_qarity ahub)
      (Zpart Zhub (drop_part 1 p0l) (shift_part p0l p0r))`;;

(* redpart proper: the fuel 12 nhub bounds the recursion (one pop per call,  *)
(* at most 4 open ranges per sector).                                        *)
let redpart_loop = new_recursive_definition num_RECURSION
 `(redpart_loop qt ahub 0 p' = F) /\
  (redpart_loop qt ahub (SUC d) p' =
  red_zpart (redpart_loop qt ahub d) ahub qt (rev_part p') p')`;;

let redpart = new_definition
 `redpart qt p <=>
    let nhub = size_part p in
    let ahub = qarity_of_nat nhub in
    nhub = nat_of_qarity ahub /\ redpart_loop qt ahub (nhub * 12) p`;;

(* ------------------------------------------------------------------------- *)
(* Part-list helpers (Coq uses seq lemmas; our parts are a custom type).     *)
(* ------------------------------------------------------------------------- *)

let CAT_PART_NIL = prove
 (`!p. cat_part p Pnil = p`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[cat_part] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let CATREV_PART_CAT = prove
 (`!p1 p2 p3. catrev_part (cat_part p1 p2) p3 =
 catrev_part p2 (catrev_part p1 p3)`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[cat_part; catrev_part] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let CATREV_CATREV = prove
 (`!p1 p2 p3. catrev_part (catrev_part p1 p2) p3 =
 catrev_part p2 (cat_part p1 p3)`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[cat_part; catrev_part] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[catrev_part]);;

let REV_REV_PART = prove
 (`!p. rev_part (rev_part p) = p`,
  REWRITE_TAC[rev_part; CATREV_CATREV; catrev_part; CAT_PART_NIL]);;

let CATREV_DROP1_TAKE1 = prove
 (`!p. catrev_part (drop_part 1 p) (take_part 1 p) = rev_part p`,
  MATCH_MP_TAC part_INDUCT THEN
  REWRITE_TAC[ONE; drop_part; take_part; catrev_part; rev_part]);;

let CATREV_TAKE1_DROP1 = prove
 (`!p. catrev_part (take_part 1 p) (drop_part 1 p) = p`,
  MATCH_MP_TAC part_INDUCT THEN
  REWRITE_TAC[ONE; drop_part; take_part; catrev_part]);;

let SIZE_SHIFT_PART = prove
 (`!p1 p2. 0 < size_part p1 ==>
 size_part (shift_part p1 p2) = SUC(size_part p2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shift_part; SIZE_CAT_PART] THEN
  MP_TAC(SPECL [`1`; `p1:part`] SIZE_TAKE_PART_LE) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> 1 <= n`] THEN ARITH_TAC);;

let ITER_FACE_ADD_ARITY = prove
 (`!(G:(A)hypermap) x n. ITER (n + arity G x) (face_map G) x =
 ITER n (face_map G) x`,
  REWRITE_TAC[GSYM ITER_ADD; ITER_FACE_ARITY_GEN]);;

let ITER_FACE_MULT_ARITY = prove
 (`!(G:(A)hypermap) x k. ITER (k * arity G x) (face_map G) x = x`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ITER; ITER_FACE_ADD_ARITY]);;

let ARITY_POS_PENTA = prove
 (`!(G:(A)hypermap) x. pentagonal G /\ x IN dart G ==>
 0 < arity G x /\ 1 <= arity G x`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PENTA_PR59) THEN
  REWRITE_TAC[mem_range] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Dart identities are decided by NORM_TAC (part_converse.ml), the e/n       *)
(* normal-form procedure; DFN_TAC adds the non-universal step: given an      *)
(* assumption `arity G s = m`, rewrite the base dart s (or its preimage) by  *)
(* ITER m f s on one side and renormalise (Coq's `rewrite [in LHS](Dfn Ds)`).*)
(* ------------------------------------------------------------------------- *)

let DFN_TAC =
  NORM_TAC THEN
  FIRST_ASSUM(fun th ->
    let l,m = dest_eq(concl th) in
    let ar,s = dest_comb l in
    let c,g = dest_comb ar in
    if fst(dest_const c) <> "arity" then failwith "DFN_TAC" else
    let thf = REWRITE_RULE[th] (ISPECL [g; s] ITER_FACE_ARITY_GEN) in
    let th1 = GSYM thf in
    let try_rw th2 =
      FIRST [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th2] THEN NORM_TAC
             THEN NO_TAC;
             GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th2] THEN
             NORM_TAC THEN NO_TAC] in
    let base_tac =
      let gmap,y = dest_comb s in
      let gc = fst(dest_const(rator gmap)) in
      let inv = if gc = "edge_map" then mk_comb(gmap, rhs(concl th1))
                else if gc = "node_map"
                then mk_comb(gmap, mk_comb(gmap, rhs(concl th1)))
                else failwith "DFN_TAC" in
      SUBGOAL_THEN (mk_eq(y, inv)) try_rw THENL
       [REWRITE_TAC[thf] THEN NORM_TAC THEN NO_TAC; ALL_TAC] in
    try_rw th1 ORELSE base_tac);;

(* ------------------------------------------------------------------------- *)
(* zvalid.                                                                   *)
(* ------------------------------------------------------------------------- *)

let ZVALID_INIT = prove
 (`!p0r. zvalid p0r (rev_part p0r) p0r`,
  REWRITE_TAC[zvalid; CATREV_PART_EQ; REV_REV_PART]);;

let ZVALID_INITL = prove
 (`!p0r. zvalid p0r (drop_part 1 (rev_part p0r))
 (shift_part (rev_part p0r) p0r)`,
  REWRITE_TAC[zvalid; shift_part; CATREV_CAT_PART; CATREV_DROP1_TAKE1;
              REV_REV_PART]);;

let ZVALID_INITR = prove
 (`!p0r. zvalid p0r (shift_part p0r (rev_part p0r)) (drop_part 1 p0r)`,
  REWRITE_TAC[zvalid; shift_part; CATREV_PART_CAT; CATREV_TAKE1_DROP1] THEN
  REWRITE_TAC[CATREV_PART_EQ; REV_REV_PART]);;

let ZVALID_SIZE = prove
 (`!p0r pl pr. zvalid p0r pl pr ==>
 size_part pl + size_part pr = 2 * size_part p0r`,
  REWRITE_TAC[zvalid] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `size_part`) THEN
  REWRITE_TAC[SIZE_CATREV_PART; SIZE_CAT_PART] THEN ARITH_TAC);;

let ZVALID_CONS = prove
 (
 `(!p0r s h pl pr. zvalid p0r (Pcons s h pl) pr <=>
  zvalid p0r pl (Pcons s h pr)) /\
   (!p0r h f1 pl pr. zvalid p0r (Pcons6 h f1 pl) pr <=>
   zvalid p0r pl (Pcons6 h f1 pr)) /\
   (!p0r h f1 f2 pl pr. zvalid p0r (Pcons7 h f1 f2 pl) pr <=>
   zvalid p0r pl (Pcons7 h f1 f2 pr)) /\
   (!p0r h f1 f2 f3 pl pr. zvalid p0r (Pcons8 h f1 f2 f3 pl) pr <=>
   zvalid p0r pl (Pcons8 h f1 f2 f3 pr))`,
  REWRITE_TAC[zvalid; catrev_part]);;

let ZVALID_FIT = prove
 (`!(G:(A)hypermap) x0 p0r pl pr.
     exact_fitp G x0 p0r /\ zvalid p0r pl pr ==>
     fitp (catrev_part pl pr) G x0`,
  REWRITE_TAC[zvalid; exact_fitp] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)
             SUBST1_TAC) THEN
  ASM_REWRITE_TAC[FITP_CAT; ITER_FACE_ARITY_GEN]);;

let ZVALID_FITR = prove
 (`!(G:(A)hypermap) x0 p0r pl pr.
     exact_fitp G x0 p0r /\ zvalid p0r pl pr ==> fitp pr G (zorg G x0 pl)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `x0:A`; `p0r:part`; `pl:part`; `pr:part`]
         ZVALID_FIT) THEN
  ASM_REWRITE_TAC[FITP_CATREV; zorg] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Shifts.                                                                   *)
(* ------------------------------------------------------------------------- *)

let ZPVALID_SHIFTL = prove
 (`!p0r zi zp. zpvalid p0r zp ==>
 zpvalid p0r (zshiftl (rev_part p0r) p0r zi zp)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  REWRITE_TAC[zpvalid; zshiftl] THEN
  STRUCT_CASES_TAC(ISPEC `a1:part` (cases "part")) THEN
  REWRITE_TAC[zshiftl_aux; zpvalid; ZVALID_INITL] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[zpvalid; ZVALID_INIT; ZVALID_CONS; IMP_CLAUSES]);;

let ZPVALID_SHIFTR = prove
 (`!p0r zi zp. zpvalid p0r zp ==>
 zpvalid p0r (zshiftr (rev_part p0r) p0r zi zp)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  REWRITE_TAC[zpvalid; zshiftr] THEN
  STRUCT_CASES_TAC(ISPEC `a2:part` (cases "part")) THEN
  REWRITE_TAC[zshiftr_aux; zpvalid; ZVALID_INITR] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[zpvalid; ZVALID_INIT; ZVALID_CONS; IMP_CLAUSES]);;

let ZPROPER_SHIFTL = prove
 (`!p0l p0r zi zp. zproper (zshiftl p0l p0r zi zp) <=> ~(zi = Znil)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  REWRITE_TAC[zshiftl] THEN
  STRUCT_CASES_TAC(ISPEC `a1:part` (cases "part")) THEN
  REWRITE_TAC[zshiftl_aux; zproper] THEN COND_CASES_TAC THEN
  REWRITE_TAC[zproper]);;

let ZPROPER_SHIFTR = prove
 (`!p0l p0r zi zp. zproper (zshiftr p0l p0r zi zp) <=> ~(zi = Znil)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  REWRITE_TAC[zshiftr] THEN
  STRUCT_CASES_TAC(ISPEC `a2:part` (cases "part")) THEN
  REWRITE_TAC[zshiftr_aux; zproper] THEN COND_CASES_TAC THEN
  REWRITE_TAC[zproper]);;

let ZSHIFTR_EQ = prove
 (`!p0l p0r zi zi' pl pr.
     1 < size_part pr
     ==> zshiftr p0l p0r zi' (Zpart zi pl pr) =
     Zpart zi' (shift_part pr pl) (drop_part 1 pr)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `pr:part` (cases "part")) THEN
  REWRITE_TAC[zshiftr; zshiftr_aux; size_part; ONE; drop_part; take_part;
              shift_part; cat_part; LT_SUC; LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[size_part; LT_REFL; LT]);;

let ZDART_SHIFTL = prove
 (`!(G:(A)hypermap) x0 p0l p0r zi zp.
     plain_cubic_pentagonal G /\ x0 IN dart G /\ size_part p0l = arity G x0
     ==> zdart G x0 (zshiftl p0l p0r zi zp) =
         zmove zi G (edge_map G (node_map G (zporg G x0 zp)))`,
  REWRITE_TAC[plain_cubic_pentagonal; plain_cubic] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  REWRITE_TAC[zshiftl; zporg] THEN
  STRUCT_CASES_TAC(ISPEC `a1:part` (cases "part")) THEN
  REWRITE_TAC[zshiftl_aux] THENL
   [ASM_REWRITE_TAC[zdart; zorg; size_part; ITER; SIZE_DROP_PART] THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `x0:A`; `1`] ITER_EN_FACE_SUBN) THEN
    ASM_SIMP_TAC[ARITY_POS_PENTA; ITER_1; o_THM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[zdart; zorg; size_part; ITER; ITER_FACE_ARITY_GEN] THEN
    NORM_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[zdart; zorg; size_part; ITER; ITER_FACE_ARITY_GEN] THEN
    NORM_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[zdart; zorg; size_part; ITER; ITER_FACE_ARITY_GEN] THEN
    NORM_TAC;
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[zdart; zorg; size_part; ITER; ITER_FACE_ARITY_GEN] THEN
    NORM_TAC]);;

let ZDART_SHIFTR = prove
 (`!(G:(A)hypermap) x0 p0r zi zp.
     plain_cubic_pentagonal G /\ x0 IN dart G /\ size_part p0r = arity G x0 /\
     zpvalid p0r zp
     ==> zdart G x0 (zshiftr (rev_part p0r) p0r zi zp) =
     zmove zi G (face_map G (zporg G x0 zp))`,
  REWRITE_TAC[plain_cubic_pentagonal; plain_cubic] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  REWRITE_TAC[zshiftr; zporg; zpvalid] THEN
  STRUCT_CASES_TAC(ISPEC `a2:part` (cases "part")) THEN
  REWRITE_TAC[zshiftr_aux] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ZVALID_SIZE) THEN
  REWRITE_TAC[size_part] THEN
  DISCH_TAC THEN
  (SUBGOAL_THEN `0 < arity (G:(A)hypermap) x0` ASSUME_TAC THENL
    [ASM_MESON_TAC[ARITY_POS_PENTA]; ALL_TAC]) THENL
   [REWRITE_TAC[zdart; zorg] THEN
    SUBGOAL_THEN `size_part a1 = 2 * arity (G:(A)hypermap) x0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p0r:part`; `rev_part p0r`] SIZE_SHIFT_PART) THEN
    ASM_REWRITE_TAC[SIZE_REV_PART] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ITER; ITER_FACE_MULT_ARITY; ITER_FACE_ARITY_GEN];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[zdart; zorg; size_part; ITER; SIZE_REV_PART;
                  ITER_FACE_ARITY_GEN] THEN
  (REFL_TAC ORELSE
   (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> rhs(concl th) = `Pnil`))
     THEN
    RULE_ASSUM_TAC(REWRITE_RULE[size_part]) THEN
    SUBGOAL_THEN `face_map G (ITER (size_part a1) (face_map G) (x0:A)) = x0`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN
      SUBGOAL_THEN `SUC(size_part a1) = 2 * arity (G:(A)hypermap) x0`
      SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[ITER_FACE_MULT_ARITY]];
      REFL_TAC])));;

(* ------------------------------------------------------------------------- *)
(* Steps: zstep[LR][t] zp fits qstep[LR] (zdart zp).                         *)
(* ------------------------------------------------------------------------- *)

let ZPROPER_STEP_TAC defs =
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  STRUCT_CASES_TAC(ISPEC `a0:zpart_loc` (cases "zpart_loc")) THEN
  REWRITE_TAC(defs @
    [zproper; ZPROPER_SHIFTL; ZPROPER_SHIFTR; distinctness "zpart_loc"]);;

let ZPROPER_STEPL = prove
 (`!p0l p0r zp. zproper (zstepL p0l p0r zp) ==> zproper zp`,
  ZPROPER_STEP_TAC [zstepL; zstepL_loc]);;
let ZPROPER_STEPR = prove
 (`!p0l p0r zp. zproper (zstepR p0l p0r zp) ==> zproper zp`,
  ZPROPER_STEP_TAC [zstepR; zstepR_loc]);;

let ZPVALID_STEP_TAC defs =
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  STRUCT_CASES_TAC(ISPEC `a0:zpart_loc` (cases "zpart_loc")) THEN
  REWRITE_TAC defs THEN
  DISCH_TAC THEN
 (FIRST [MATCH_MP_TAC ZPVALID_SHIFTL; MATCH_MP_TAC ZPVALID_SHIFTR;
         ALL_TAC]) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[zpvalid];;

let ZPVALID_STEPL = prove
 (`!p0r zp. zpvalid p0r zp ==> zpvalid p0r (zstepL (rev_part p0r) p0r zp)`,
  ZPVALID_STEP_TAC [zstepL; zstepL_loc]);;
let ZPVALID_STEPR = prove
 (`!p0r zp. zpvalid p0r zp ==> zpvalid p0r (zstepR (rev_part p0r) p0r zp)`,
  ZPVALID_STEP_TAC [zstepR; zstepR_loc]);;
let ZPVALID_STEPLT = prove
 (`!p0r zp. zpvalid p0r zp ==> zpvalid p0r (zstepLt (rev_part p0r) p0r zp)`,
  ZPVALID_STEP_TAC [zstepLt; zstepLt_loc]);;
let ZPVALID_STEPRT = prove
 (`!p0r zp. zpvalid p0r zp ==> zpvalid p0r (zstepRt (rev_part p0r) p0r zp)`,
  ZPVALID_STEP_TAC [zstepRt; zstepRt_loc]);;

(* Universal cases close by normalisation; the Zhat/Zhatl/Zhatr cases need   *)
(* the spoke arity (from fitp of the right part at zorg pl, resp. of the     *)
(* left part at zorg (tail pl)) and DFN_TAC.                                 *)
let ZSTEP_DIRECT = REWRITE_TAC[zdart; zmove; zporg; qstepL; qstepR] THEN
NORM_TAC THEN NO_TAC;;

let ZSTEP_SETUP =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[zpvalid; plain_cubic_pentagonal; plain_cubic] THEN STRIP_TAC THEN
  SUBGOAL_THEN `size_part p0r = arity (G:(A)hypermap) x0` ASSUME_TAC THENL
   [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!zj zk. zdart (G:(A)hypermap) x0
    (zshiftl (rev_part p0r) p0r zj (Zpart zk pl pr)) =
            zmove zj G (edge_map G (node_map G (zorg G x0 pl)))`
            ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL
      [`G:(A)hypermap`; `x0:A`; `rev_part p0r`; `p0r:part`; `zj:zpart_loc`;
                   `Zpart zk pl pr`] ZDART_SHIFTL) THEN
    ASM_REWRITE_TAC[plain_cubic_pentagonal; plain_cubic; SIZE_REV_PART; zporg];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!zj zk. zdart (G:(A)hypermap) x0
    (zshiftr (rev_part p0r) p0r zj (Zpart zk pl pr)) =
            zmove zj G (face_map G (zorg G x0 pl))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL
      [`G:(A)hypermap`; `x0:A`; `p0r:part`; `zj:zpart_loc`; `Zpart zk pl pr`]
                  ZDART_SHIFTR) THEN
    ASM_REWRITE_TAC[plain_cubic_pentagonal; plain_cubic; zpvalid; zporg];
    ALL_TAC] THEN
  SUBGOAL_THEN `fitp pr (G:(A)hypermap) (zorg G x0 pl)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ZVALID_FITR]; ALL_TAC];;

let ZCASE_PR_TAC =
  UNDISCH_TAC `fitp pr (G:(A)hypermap) (zorg G x0 pl)` THEN
  STRUCT_CASES_TAC(ISPEC `pr:part` (cases "part")) THEN
  REWRITE_TAC[zfanL; zfanR; fitp; subpart_loc_move;
              distinctness "zpart_loc"] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "zpart_loc"]) THEN
  REWRITE_TAC[mem_range] THEN STRIP_TAC THEN
  REWRITE_TAC[zdart; zmove; qstepL; qstepR] THEN DFN_TAC;;

let ZCASE_PL_TAC =
  UNDISCH_TAC `zvalid p0r pl pr` THEN
  STRUCT_CASES_TAC(ISPEC `pl:part` (cases "part")) THEN
  REWRITE_TAC[zfanL; zfanR; distinctness "zpart_loc"; ZVALID_CONS] THEN
  DISCH_THEN(fun th ->
    MP_TAC(MATCH_MP ZVALID_FITR
      (CONJ (ASSUME `exact_fitp (G:(A)hypermap) x0 p0r`) th))) THEN
  REWRITE_TAC[fitp; subpart_loc_move; zorg; size_part; ITER] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "zpart_loc"]) THEN
  REWRITE_TAC[mem_range] THEN STRIP_TAC THEN
  REWRITE_TAC[zdart; zmove; qstepL; qstepR; zorg; size_part; ITER] THEN
  DFN_TAC;;

let ZDART_STEPL_ZPART = prove
 (`!(G:(A)hypermap) x0 p0r zi pl pr.
     plain_cubic_pentagonal G /\ x0 IN dart G /\ exact_fitp G x0 p0r /\
     zpvalid p0r (Zpart zi pl pr)
     ==> zpfit G x0 (qstepL G (zdart G x0 (Zpart zi pl pr)))
     (zstepL (rev_part p0r) p0r (Zpart zi pl pr))`,
  ZSTEP_SETUP THEN
  STRUCT_CASES_TAC(ISPEC `zi:zpart_loc` (cases "zpart_loc")) THEN
  REWRITE_TAC[zstepL; zstepL_loc; zpfit; zproper; ZPROPER_SHIFTL;
              ZPROPER_SHIFTR; distinctness "zpart_loc"] THEN
  ASM_REWRITE_TAC[] THEN TRY ZSTEP_DIRECT THENL
   [ZCASE_PR_TAC; ZCASE_PL_TAC]);;

let ZDART_STEPR_ZPART = prove
 (`!(G:(A)hypermap) x0 p0r zi pl pr.
     plain_cubic_pentagonal G /\ x0 IN dart G /\ exact_fitp G x0 p0r /\
     zpvalid p0r (Zpart zi pl pr)
     ==> zpfit G x0 (qstepR G (zdart G x0 (Zpart zi pl pr)))
     (zstepR (rev_part p0r) p0r (Zpart zi pl pr))`,
  ZSTEP_SETUP THEN
  STRUCT_CASES_TAC(ISPEC `zi:zpart_loc` (cases "zpart_loc")) THEN
  REWRITE_TAC[zstepR; zstepR_loc; zpfit; zproper; ZPROPER_SHIFTL;
              ZPROPER_SHIFTR; distinctness "zpart_loc"] THEN
  ASM_REWRITE_TAC[] THEN TRY ZSTEP_DIRECT THENL
   [ZCASE_PL_TAC; ZCASE_PR_TAC]);;

(* The t variants: only Zhatl (resp. Zhatr) differs; there zpfit_top fixes   *)
(* the spoke arity to the top of its range.                                  *)
let ZCASE_TOP_TAC v =
  REWRITE_TAC[zpfit_top; zrange; zrange_loc; zpfit; zproper; ZPROPER_SHIFTL;
              ZPROPER_SHIFTR] THEN
  ASM_REWRITE_TAC[] THEN STRUCT_CASES_TAC(ISPEC v (cases "part")) THEN
  REWRITE_TAC[zfanLt; zfanRt; get_spoke; distinctness "zpart_loc"] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "zpart_loc"]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check
    (is_disj o concl))) THEN
  REWRITE_TAC[topqa; nat_of_qarity; zdart; zmove; qstepL; qstepR; zorg;
              size_part; ITER] THEN
  DISCH_TAC THEN DFN_TAC;;

let ZDART_STEPLT_ZPART = prove
 (`!(G:(A)hypermap) x0 p0r ahub zi pl pr.
     plain_cubic_pentagonal G /\ x0 IN dart G /\ exact_fitp G x0 p0r /\
     zpvalid p0r (Zpart zi pl pr) /\
     zpfit_top G x0 ahub (Zpart zi pl pr)
     ==> zpfit G x0 (qstepL G (zdart G x0 (Zpart zi pl pr)))
     (zstepLt (rev_part p0r) p0r (Zpart zi pl pr))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
 [`G:(A)hypermap`; `x0:A`; `p0r:part`; `zi:zpart_loc`; `pl:part`; `pr:part`
 ] ZDART_STEPL_ZPART) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `zpfit_top (G:(A)hypermap) x0 ahub (Zpart zi pl pr)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[plain_cubic_pentagonal; plain_cubic] o
              check (fun th -> concl th = `plain_cubic_pentagonal
                     (G:(A)hypermap)`)) THEN
  STRUCT_CASES_TAC(ISPEC `zi:zpart_loc` (cases "zpart_loc")) THEN
  REWRITE_TAC[zstepL; zstepL_loc; zstepLt; zstepLt_loc] THEN
  TRY(DISCH_THEN(K ALL_TAC) THEN DISCH_THEN ACCEPT_TAC) THEN
  DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN MP_TAC th) THEN
  ZCASE_TOP_TAC `pl:part`);;

let ZDART_STEPRT_ZPART = prove
 (`!(G:(A)hypermap) x0 p0r ahub zi pl pr.
     plain_cubic_pentagonal G /\ x0 IN dart G /\ exact_fitp G x0 p0r /\
     zpvalid p0r (Zpart zi pl pr) /\
     zpfit_top G x0 ahub (Zpart zi pl pr)
     ==> zpfit G x0 (qstepR G (zdart G x0 (Zpart zi pl pr)))
     (zstepRt (rev_part p0r) p0r (Zpart zi pl pr))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zpvalid] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
 [`G:(A)hypermap`; `x0:A`; `p0r:part`; `zi:zpart_loc`; `pl:part`; `pr:part`
 ] ZDART_STEPR_ZPART) THEN
  ASM_REWRITE_TAC[zpvalid] THEN
  UNDISCH_TAC `zpfit_top (G:(A)hypermap) x0 ahub (Zpart zi pl pr)` THEN
  SUBGOAL_THEN `size_part p0r = arity (G:(A)hypermap) x0` ASSUME_TAC THENL
   [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!zj zk. zdart (G:(A)hypermap) x0
    (zshiftr (rev_part p0r) p0r zj (Zpart zk pl pr)) =
            zmove zj G (face_map G (zorg G x0 pl))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL
      [`G:(A)hypermap`; `x0:A`; `p0r:part`; `zj:zpart_loc`; `Zpart zk pl pr`]
                  ZDART_SHIFTR) THEN
    ASM_REWRITE_TAC[zpvalid; zporg]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[plain_cubic_pentagonal; plain_cubic] o
              check (fun th -> concl th = `plain_cubic_pentagonal
                     (G:(A)hypermap)`)) THEN
  STRUCT_CASES_TAC(ISPEC `zi:zpart_loc` (cases "zpart_loc")) THEN
  REWRITE_TAC[zstepR; zstepR_loc; zstepRt; zstepRt_loc] THEN
  TRY(DISCH_THEN(K ALL_TAC) THEN DISCH_THEN ACCEPT_TAC) THEN
  DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN MP_TAC th) THEN
  ZCASE_TOP_TAC `pr:part`);;

(* ------------------------------------------------------------------------- *)
(* fitqa.                                                                    *)
(* ------------------------------------------------------------------------- *)

let FITQA_PR59 = prove
 (`!qa. ~(fitqa Pr59 qa)`,
  GEN_TAC THEN REWRITE_TAC[fitqa; topqa] THEN
  STRUCT_CASES_TAC(ISPEC `qa:qarity` (cases "qarity")) THEN
  REWRITE_TAC[nat_of_qarity; distinctness "qarity"] THEN ARITH_TAC);;

let FITQA_PROPER = prove
 (`!ahub zp qa. fitqa (zrange ahub zp) qa ==> zproper zp`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  REWRITE_TAC[zproper; zrange] THEN ASM_CASES_TAC `a0 = Znil` THEN
  ASM_REWRITE_TAC[zrange_loc; FITQA_PR59]);;

let FITQA_POPQA = prove
 (`!r qa. fitqa r qa
          ==> !n. mem_range r n /\
          (mem_range (popqa r) 9 \/ ~mem_range (popqa r) n)
                  ==> n = nat_of_qarity qa`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:prange` (cases "prange")) THEN
  STRUCT_CASES_TAC(ISPEC `qa:qarity` (cases "qarity")) THEN
  REWRITE_TAC[fitqa; topqa; popqa; mem_range; nat_of_qarity;
              distinctness "qarity"] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The RedpartRec section hypotheses, bundled (G, nhub, red_rec, p0r, x0).   *)
(* ------------------------------------------------------------------------- *)

let redpart_hyps = new_definition
 `redpart_hyps (G:(A)hypermap) nhub (red_rec:part->bool) p0r x0 <=>
    plain_cubic_pentagonal G /\
    (!x p. x IN dart G /\ arity G x = nhub /\ exact_fitp G x p ==> ~red_rec p)
    /\
    x0 IN dart G /\ exact_fitp G x0 p0r /\ arity G x0 = nhub`;;

(* Coq RED_PCONS_FIT: popping a fitted range pc r pr (part_update G pc j)    *)
(* and padding with p0r gives a part of size nhub that fits at zorg pl;      *)
(* since red_rec rejects it, the arity at location j must be the top of the  *)
(* range.                                                                    *)
let RED_PCONS_FIT = prove
 (`!(G:(A)hypermap) nhub (red_rec:part->bool) p0r x0 (pc:prange->part->part)
 j r pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\
     part_update G pc j /\ zvalid p0r pl (pc r pr) /\ fitqa r qa /\
     red_pcons red_rec nhub p0r pc r pr
     ==> arity G (subpart_loc_move j G (zorg G x0 pl)) = nat_of_qarity qa`,
  REWRITE_TAC[redpart_hyps] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `size_part p0r = nhub` ASSUME_TAC THENL
  [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  SUBGOAL_THEN `fitp p0r G (x0:A)` ASSUME_TAC THENL
  [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  UNDISCH_TAC `part_update (G:(A)hypermap) pc j` THEN
  REWRITE_TAC[part_update] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(GEN_ALL(CONJUNCT1(SPEC_ALL th))) THEN
                       ASSUME_TAC(GEN_ALL(CONJUNCT2(SPEC_ALL th)))) THEN
  SUBGOAL_THEN `fitp ((pc:prange->part->part) r pr) G (zorg G x0 pl:A)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ZVALID_FITR]; ALL_TAC] THEN
  SUBGOAL_THEN `arity G (zorg G x0 pl:A) = nhub` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[zorg; ARITY_ITER_FACE_GEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(zorg G x0 pl:A) IN dart G` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[zorg; ITER_FACE_IN_DART_EQ]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`r:prange`; `pr:part`; `zorg G x0 pl:A`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`r:prange`; `qa:qarity`] FITQA_POPQA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC
   `mem_range (popqa r) (arity G (subpart_loc_move j G (zorg G x0 pl:A)))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `fitp ((pc:prange->part->part) (popqa r) pr) G (zorg G x0 pl:A)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `exact_fitp G (zorg G x0 pl:A)
    (take_part nhub (cat_part ((pc:prange->part->part) (popqa r) pr) p0r))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
 `fitp (cat_part ((pc:prange->part->part) (popqa r) pr) p0r) G
  (zorg G x0 pl:A)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[FITP_CAT; zorg; ITER_ADD] THEN
      SUBGOAL_THEN `SUC(size_part pr) + size_part pl = 2 * arity G (x0:A)`
      SUBST1_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP ZVALID_SIZE) THEN
       ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ASM_REWRITE_TAC[ITER_FACE_MULT_ARITY]];
      DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE
        [GSYM(SPECL [`nhub:num`;
                     `cat_part ((pc:prange->part->part) (popqa r) pr) p0r`]
                    CAT_TAKE_DROP_PART)]) THEN
      REWRITE_TAC[FITP_CAT; exact_fitp] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIZE_TAKE_PART_LE THEN
      ASM_REWRITE_TAC[SIZE_CAT_PART] THEN ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`zorg (G:(A)hypermap) x0 pl`;
                              `take_part nhub
                  (cat_part ((pc:prange->part->part) (popqa r) pr) p0r)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `red_pcons red_rec nhub p0r pc r pr` THEN
  REWRITE_TAC[red_pcons; LET_DEF; LET_END_DEF] THEN
  STRUCT_CASES_TAC(ISPEC `r:prange` (cases "prange")) THEN
  REWRITE_TAC[distinctness "prange"; popqa; mem_range; LE_REFL] THEN
  MESON_TAC[]);;

let FITQA_SINGLETON = prove
 (`(!qa. fitqa Pr55 qa <=> qa = Qa5) /\ (!qa. fitqa Pr66 qa <=> qa = Qa6) /\
   (!qa. fitqa Pr77 qa <=> qa = Qa7) /\ (!qa. fitqa Pr88 qa <=> qa = Qa8)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `qa:qarity` (cases "qarity")) THEN
  REWRITE_TAC[fitqa; topqa; nat_of_qarity; distinctness "qarity"] THEN
  ARITH_TAC);;

(* The eleven part_update lemmas, eta-reduced to match the lambdas used in   *)
(* the red_pop definitions.                                                  *)
let UPD_ETA = map (REWRITE_RULE[ETA_AX])
  [UPDATEPS; UPDATEPH; UPDATEP6H; UPDATEP6F1; UPDATEP7H;
   UPDATEP7F1; UPDATEP7F2;
   UPDATEP8H; UPDATEP8F1; UPDATEP8F2; UPDATEP8F3];;

(* ------------------------------------------------------------------------- *)
(* The ten pop-fit lemmas: one uniform tactic. POPFIT_TAC v splits the part  *)
(* v (pr for the right lemmas, pl for the left ones), derives the fitp of    *)
(* the relevant subpart from the zvalid assumption (FIT_TAC), and either     *)
(* closes directly (singleton ranges) or applies RED_PCONS_FIT with the pc / *)
(* range / tail read off the red_pcons assumption, trying the 5 subpart      *)
(* locations.                                                                *)
(* ------------------------------------------------------------------------- *)

let POPFIT_DEFS =
  [get_spoke; get_hat; next_hat; get_fan1l; get_fan2l; get_fan3l; get_fan1r;
   get_fan2r; get_fan3r;
   red_popr_spoke; red_popr_hat; red_popl_spoke; red_popl_hat; red_popl_fan1l;
   red_popl_fan2l;
   red_popl_fan3l; red_popl_fan1r; red_popl_fan2r; red_popl_fan3r; FITQA_PR59;
   FITQA_SINGLETON;
   ZVALID_CONS; ETA_AX];;

let FIT_TAC =
  FIRST_ASSUM(fun zv ->
    let g,_ = strip_comb(concl zv) in
    if not(is_const g) || fst(dest_const g) <> "zvalid"
    then failwith "FIT_TAC" else
    MP_TAC(MATCH_MP ZVALID_FITR
      (CONJ (ASSUME `exact_fitp (G:(A)hypermap) x0 p0r`) zv))) THEN
  REWRITE_TAC[fitp; subpart_loc_move; mem_range; zorg; size_part; ITER] THEN
  STRIP_TAC;;

let RED_PCONS_TAC =
  FIRST_ASSUM(fun th ->
    let f,args = strip_comb(concl th) in
    if not(is_const f) || fst(dest_const f) <> "red_pcons"
    then failwith "RED_PCONS_TAC" else
    let rr,nh,p0,pc,r,pr' =
      (match args with
      [a;b;c;d;e;f] -> a,b,c,d,e,f | _ -> failwith "RED_PCONS_TAC") in
    FIRST_ASSUM(fun zv ->
      let g,zargs = strip_comb(concl zv) in
      if not(is_const g) || fst(dest_const g) <> "zvalid"
      then failwith "RED_PCONS_TAC" else
      let pl = el 1 zargs in
      FIRST (map (fun j ->
        MP_TAC(ISPECL
          [`G:(A)hypermap`; nh; rr; p0; `x0:A`; pc; j; r; pl; pr'; `qa:qarity`]
                      RED_PCONS_FIT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC UPD_ETA THEN NO_TAC; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[subpart_loc_move; zdart; zmove; zorg; size_part; ITER] THEN
        ((NORM_TAC THEN NO_TAC) ORELSE DFN_TAC))
       [`Pspoke`; `Phat`; `Pfan1`; `Pfan2`; `Pfan3`])));;

let POPFIT_TAC v =
  REWRITE_TAC[redpart_hyps; plain_cubic_pentagonal; plain_cubic] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `redpart_hyps (G:(A)hypermap) nhub red_rec p0r x0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[redpart_hyps; plain_cubic_pentagonal; plain_cubic];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in v (concl th)))) THEN
  STRUCT_CASES_TAC(ISPEC v (cases "part")) THEN REWRITE_TAC POPFIT_DEFS THEN
  REPEAT STRIP_TAC THEN
  FIT_TAC THEN REWRITE_TAC[zdart; zmove; zorg; size_part; ITER] THEN
  ((NORM_TAC THEN ASM_REWRITE_TAC[nat_of_qarity] THEN NO_TAC) ORELSE
  RED_PCONS_TAC);;

let RED_POPR_SPOKE_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_spoke pr) qa /\ red_popr_spoke red_rec nhub p0r pr
     ==> arity G (edge_map G (zorg G x0 pl)) = nat_of_qarity qa`,
  POPFIT_TAC `pr:part`);;

let RED_POPR_HAT_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_hat pr) qa /\ red_popr_hat red_rec nhub p0r pr
     ==> arity G (edge_map G (ITER 2 (face_map G) (edge_map G (zorg G x0 pl))))
     = nat_of_qarity qa`,
  POPFIT_TAC `pr:part`);;

let RED_POPL_SPOKE_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_spoke pl) qa /\ red_popl_spoke red_rec nhub p0r pl pr
     ==> arity G (node_map G (zorg G x0 pl)) = nat_of_qarity qa`,
  POPFIT_TAC `pl:part`);;

let RED_POPL_HAT_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_hat pl) qa /\ red_popl_hat red_rec nhub p0r pl pr
     ==> arity G (edge_map G (ITER 2 (face_map G) (node_map G (zorg G x0 pl))))
     = nat_of_qarity qa`,
  POPFIT_TAC `pl:part`);;

let RED_POPL_FAN1L_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_fan1l pl) qa /\ red_popl_fan1l red_rec nhub p0r pl pr
     ==> arity G (zdart G x0 (Zpart Zfan1l pl pr)) = nat_of_qarity qa`,
  POPFIT_TAC `pl:part`);;

let RED_POPL_FAN2L_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_fan2l pl) qa /\ red_popl_fan2l red_rec nhub p0r pl pr
     ==> arity G (zdart G x0 (Zpart Zfan2l pl pr)) = nat_of_qarity qa`,
  POPFIT_TAC `pl:part`);;

let RED_POPL_FAN3L_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_fan3l pl) qa /\ red_popl_fan3l red_rec nhub p0r pl pr
     ==> arity G (zdart G x0 (Zpart Zfan3l pl pr)) = nat_of_qarity qa`,
  POPFIT_TAC `pl:part`);;

let RED_POPL_FAN1R_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_fan1r pl) qa /\ red_popl_fan1r red_rec nhub p0r pl pr
     ==> arity G (zdart G x0 (Zpart Zfan1r pl pr)) = nat_of_qarity qa`,
  POPFIT_TAC `pl:part`);;

let RED_POPL_FAN2R_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_fan2r pl) qa /\ red_popl_fan2r red_rec nhub p0r pl pr
     ==> arity G (zdart G x0 (Zpart Zfan2r pl pr)) = nat_of_qarity qa`,
  POPFIT_TAC `pl:part`);;

let RED_POPL_FAN3R_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 pl pr qa.
     redpart_hyps G nhub red_rec p0r x0 /\ zvalid p0r pl pr /\
     fitqa (get_fan3r pl) qa /\ red_popl_fan3r red_rec nhub p0r pl pr
     ==> arity G (zdart G x0 (Zpart Zfan3r pl pr)) = nat_of_qarity qa`,
  POPFIT_TAC `pl:part`);;

(* ------------------------------------------------------------------------- *)
(* RED_POP_FIT, then zp-level corollaries used by FITQZP_FIT.                *)
(* ------------------------------------------------------------------------- *)

let FITQA_HUB_RANGE = prove
 (`!ahub qa. fitqa (hub_range ahub) qa ==>
 nat_of_qarity qa = nat_of_qarity ahub`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ahub:qarity` (cases "qarity")) THEN
  STRUCT_CASES_TAC(ISPEC `qa:qarity` (cases "qarity")) THEN
  REWRITE_TAC[hub_range; fitqa; topqa; nat_of_qarity;
              distinctness "qarity"] THEN
  ARITH_TAC);;

let RED_POP_CASE_TAC =
  FIRST (map (fun lem ->
    MP_TAC(ISPECL
      [`G:(A)hypermap`; `nhub:num`; `red_rec:part->bool`; `p0r:part`; `x0:A`;
                   `pl:part`; `pr:part`; `qa:qarity`] lem) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[zdart; zmove] THEN
    NORM_TAC THEN NO_TAC)
   [RED_POPR_SPOKE_FIT; RED_POPR_HAT_FIT; RED_POPL_SPOKE_FIT; RED_POPL_HAT_FIT;
    RED_POPL_FAN1L_FIT; RED_POPL_FAN2L_FIT; RED_POPL_FAN3L_FIT;
    RED_POPL_FAN1R_FIT; RED_POPL_FAN2R_FIT; RED_POPL_FAN3R_FIT]);;

(* The zpart cases with named components zi pl pr.                           *)
let ZPART_CASES_TAC =
  MP_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN
  DISCH_THEN(X_CHOOSE_THEN `zi:zpart_loc`
   (X_CHOOSE_THEN `pl:part` (X_CHOOSE_THEN `pr:part` SUBST1_TAC)));;

let RED_POP_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 ahub zp qa.
     redpart_hyps G nhub red_rec p0r x0 /\ nhub = nat_of_qarity ahub /\
     zpvalid p0r zp /\
     fitqa (zrange ahub zp) qa /\ red_pop red_rec nhub p0r zp
     ==> arity G (zdart G x0 zp) = nat_of_qarity qa`,
  REPEAT GEN_TAC THEN ZPART_CASES_TAC THEN
  REWRITE_TAC[zpvalid; zrange; red_pop] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[redpart_hyps; plain_cubic_pentagonal; plain_cubic] o
              check (fun th -> concl th = `redpart_hyps (G:(A)hypermap) nhub
                     red_rec p0r x0`)) THEN
  UNDISCH_TAC `red_pop_loc red_rec nhub p0r zi pl pr` THEN
  UNDISCH_TAC `fitqa (zrange_loc ahub zi pl pr) qa` THEN
  STRUCT_CASES_TAC(ISPEC `zi:zpart_loc` (cases "zpart_loc")) THEN
  REWRITE_TAC[zrange_loc; red_pop_loc; FITQA_PR59] THEN REPEAT DISCH_TAC THEN
  (RED_POP_CASE_TAC ORELSE
   (REWRITE_TAC[zdart; zmove; zorg; ARITY_ITER_FACE_GEN] THEN
   ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FITQA_HUB_RANGE THEN
    ASM_REWRITE_TAC[])));;

let ZDART_STEPL = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 zp.
     redpart_hyps G nhub red_rec p0r x0 /\ zpvalid p0r zp
     ==> zpfit G x0 (qstepL G (zdart G x0 zp)) (zstepL (rev_part p0r) p0r zp)`,
  REWRITE_TAC[redpart_hyps] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN STRIP_TAC THEN
  MATCH_MP_TAC ZDART_STEPL_ZPART THEN ASM_REWRITE_TAC[]);;

let ZDART_STEPR = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 zp.
     redpart_hyps G nhub red_rec p0r x0 /\ zpvalid p0r zp
     ==> zpfit G x0 (qstepR G (zdart G x0 zp)) (zstepR (rev_part p0r) p0r zp)`,
  REWRITE_TAC[redpart_hyps] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN STRIP_TAC THEN
  MATCH_MP_TAC ZDART_STEPR_ZPART THEN ASM_REWRITE_TAC[]);;

let ZDART_STEPLT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 ahub zp.
     redpart_hyps G nhub red_rec p0r x0 /\ zpvalid p0r zp /\
     zpfit_top G x0 ahub zp
     ==> zpfit G x0 (qstepL G (zdart G x0 zp))
                   (zstepLt (rev_part p0r) p0r zp)`,
  REWRITE_TAC[redpart_hyps] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `x0:A`; `p0r:part`; `ahub:qarity`;
                 `a0:zpart_loc`; `a1:part`; `a2:part`] ZDART_STEPLT_ZPART) THEN
  ASM_REWRITE_TAC[]);;

let ZDART_STEPRT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 ahub zp.
     redpart_hyps G nhub red_rec p0r x0 /\ zpvalid p0r zp /\
     zpfit_top G x0 ahub zp
     ==> zpfit G x0 (qstepR G (zdart G x0 zp))
                   (zstepRt (rev_part p0r) p0r zp)`,
  REWRITE_TAC[redpart_hyps] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `zp:zpart` (cases "zpart")) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `x0:A`; `p0r:part`; `ahub:qarity`;
                 `a0:zpart_loc`; `a1:part`; `a2:part`] ZDART_STEPRT_ZPART) THEN
  ASM_REWRITE_TAC[]);;

let ZPFIT_TOP_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 ahub zp qa.
     redpart_hyps G nhub red_rec p0r x0 /\ nhub = nat_of_qarity ahub /\
     zpvalid p0r zp /\
     fitqa (zrange ahub zp) qa /\ red_pop red_rec nhub p0r zp
     ==> zpfit_top G x0 ahub zp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[zpfit_top] THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `nhub:num`; `red_rec:part->bool`; `p0r:part`;
                 `x0:A`; `ahub:qarity`; `zp:zpart`; `qa:qarity`]
         RED_POP_FIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `fitqa (zrange ahub zp) qa` THEN REWRITE_TAC[fitqa] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* fitqzp.                                                                   *)
(* ------------------------------------------------------------------------- *)

let FITQ_CLAUSES = prove
 (`!(H:(A)hypermap) x.
     (fitq H x Qask0 <=> T) /\
     (!qa. fitq H x (Qask1 qa) <=> nat_of_qarity qa = arity H x) /\
     (!qa ql. fitq H x (QaskL qa ql) <=>
     nat_of_qarity qa = arity H x /\ fitq H (qstepL H x) ql) /\
     (!qa qr. fitq H x (QaskR qa qr) <=>
     nat_of_qarity qa = arity H x /\ fitq H (qstepR H x) qr) /\
     (!qa ql qr. fitq H x (QaskLR qa ql qr) <=>
        nat_of_qarity qa = arity H x /\ fitq H (qstepL H x) ql /\
        fitq H (qstepR H x) qr) /\
     (!qa qll. fitq H x (QaskLL qa qll) <=>
        nat_of_qarity qa = arity H (edge_map H (node_map H (qstepL H x))) /\
        fitq H (qstepL H (qstepL H x)) qll) /\
     (!qa qrr. fitq H x (QaskRR qa qrr) <=>
        nat_of_qarity qa = arity H (qstepR H x) /\
        fitq H (qstepR H (qstepR H x)) qrr)`,
  REWRITE_TAC[fitq; flatq; walkq; MAP; CONS_11; FITQ_CAT] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC]);;

let FITQZP_PROPER = prove
 (`!ahub p0l p0r q zp. fitqzp ahub p0l p0r q zp ==> q = Qask0 \/ zproper zp`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `q:question` (cases "question")) THEN
  REWRITE_TAC[fitqzp; distinctness "question"; IF_F] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[FITQA_PROPER; ZPROPER_STEPL; ZPROPER_STEPR]);;

let HARGS = [`G:(A)hypermap`; `nhub:num`; `red_rec:part->bool`;
             `p0r:part`; `x0:A`];;

let ARITY_TAC zp' a =
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL (HARGS @ [`ahub:qarity`; zp'; a]) RED_POP_FIT) THEN
  ASM_REWRITE_TAC[] THEN NO_TAC;;

let PROPER_SPLIT_TAC q zp' =
  MP_TAC(ISPECL [`ahub:qarity`; `rev_part p0r`; `p0r:part`; q; zp']
    FITQZP_PROPER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* A question asked at the child zp' of zp (a zstep, with its zpvalid lemma  *)
(* vthm): either the question is Qask0, or zp' is proper, the dart of zp'    *)
(* is the qstep of that of zp (dthm, instantiated at HARGS @ args), and the  *)
(* induction hypothesis applies.                                             *)
let CHILD_TAC q zp' dthm args vthm =
  PROPER_SPLIT_TAC q zp' THENL
   [ASM_REWRITE_TAC[FITQ_CLAUSES];
    MP_TAC(ISPECL (HARGS @ args) dthm) THEN ASM_REWRITE_TAC[zpfit] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC vthm THEN ASM_REWRITE_TAC[]];;

(* Coq FITQZP_FIT: induction on the question.                                *)
let FITQZP_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 ahub.
     redpart_hyps G nhub red_rec p0r x0 /\ nhub = nat_of_qarity ahub
     ==> !q zp. fitqzp ahub (rev_part p0r) p0r q zp /\
                red_popqzp red_rec nhub (rev_part p0r) p0r q zp /\
                zpvalid p0r zp
                ==> fitq G (zdart G x0 zp) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC question_INDUCT THEN
  REWRITE_TAC[fitqzp; red_popqzp; FITQ_CLAUSES; IF_F] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ARITY_TAC `zp:zpart` `a:qarity`;
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL [ARITY_TAC `zp:zpart` `a0:qarity`; ALL_TAC] THEN
    MP_TAC(ISPECL (HARGS @ [`ahub:qarity`; `zp:zpart`; `a0:qarity`])
           ZPFIT_TOP_FIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CHILD_TAC `a1:question` `zstepLt (rev_part p0r) p0r zp` ZDART_STEPLT
              [`ahub:qarity`; `zp:zpart`] ZPVALID_STEPLT;
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL [ARITY_TAC `zp:zpart` `a0:qarity`; ALL_TAC] THEN
    MP_TAC(ISPECL (HARGS @ [`ahub:qarity`; `zp:zpart`; `a0:qarity`])
           ZPFIT_TOP_FIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CHILD_TAC `a1:question` `zstepRt (rev_part p0r) p0r zp` ZDART_STEPRT
              [`ahub:qarity`; `zp:zpart`] ZPVALID_STEPRT;
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ARITY_TAC `zp:zpart` `a0:qarity`;
      CHILD_TAC `a1:question` `zstepL (rev_part p0r) p0r zp` ZDART_STEPL
                [`zp:zpart`] ZPVALID_STEPL;
      CHILD_TAC `a2:question` `zstepR (rev_part p0r) p0r zp` ZDART_STEPR
                [`zp:zpart`] ZPVALID_STEPR];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `zpvalid p0r (zstepL (rev_part p0r) p0r zp) /\
                  zproper (zstepL (rev_part p0r) p0r zp)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ZPVALID_STEPL] THEN ASM_MESON_TAC[FITQA_PROPER];
      ALL_TAC] THEN
    MP_TAC(ISPECL (HARGS @ [`zp:zpart`]) ZDART_STEPL) THEN
    ASM_REWRITE_TAC[zpfit] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[ARITY_EN_U] THEN
    CONJ_TAC THENL
     [ARITY_TAC `zstepL (rev_part p0r) p0r zp` `a0:qarity`;
      CHILD_TAC `a1:question`
                `zstepL (rev_part p0r) p0r (zstepL (rev_part p0r) p0r zp)`
                ZDART_STEPL [`zstepL (rev_part p0r) p0r zp`] ZPVALID_STEPL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `zpvalid p0r (zstepR (rev_part p0r) p0r zp) /\
                  zproper (zstepR (rev_part p0r) p0r zp)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ZPVALID_STEPR] THEN ASM_MESON_TAC[FITQA_PROPER];
      ALL_TAC] THEN
    MP_TAC(ISPECL (HARGS @ [`zp:zpart`]) ZDART_STEPR) THEN
    ASM_REWRITE_TAC[zpfit] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ARITY_TAC `zstepR (rev_part p0r) p0r zp` `a0:qarity`;
      CHILD_TAC `a1:question`
                `zstepR (rev_part p0r) p0r (zstepR (rev_part p0r) p0r zp)`
                ZDART_STEPR [`zstepR (rev_part p0r) p0r zp`] ZPVALID_STEPR]]);;

(* ------------------------------------------------------------------------- *)
(* red_qzt_leaf, qzt_getr, and the no-fit lemma for the quiz tree.           *)
(* ------------------------------------------------------------------------- *)

let LEAF_REC_TAC =
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  STRIP_TAC THEN
  GEN_TAC THEN STRIP_TAC THEN DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[];;

let LEAF_FIT_TAC q zp tgt =
  PROPER_SPLIT_TAC q zp THENL
   [ASM_REWRITE_TAC[FITQ_CLAUSES];
    SUBGOAL_THEN
     (mk_eq(list_mk_comb(`zdart:(A)hypermap->A->zpart->A`,
                         [`G:(A)hypermap`; `x0:A`; zp]), tgt))
     (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[zpfit];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];;

let LEAF_ALL_TAC =
  STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN DISJ1_TAC THEN
  MP_TAC(ISPECL (HARGS @ [`ahub:qarity`]) FITQZP_FIT) THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [LEAF_FIT_TAC `a0:question` `zp1:zpart` `qstepR (G:(A)hypermap) x`;
    LEAF_FIT_TAC `a1:question` `zp2:zpart`
    `qstepR (G:(A)hypermap) (node_map G x)`;
    LEAF_FIT_TAC `a2:question` `zp3:zpart`
    `qstepR (G:(A)hypermap) (node_map G (node_map G x))`];;

let RED_QZT_LEAF_FIT = prove
 (`!(G:(A)hypermap) nhub red_rec p0r x0 ahub.
     redpart_hyps G nhub red_rec p0r x0 /\ nhub = nat_of_qarity ahub
     ==> !zp1 zp2 zp3 qtl.
           red_qzt_leaf red_rec nhub ahub (rev_part p0r) p0r zp1 zp2 zp3 qtl
           ==> qzt_proper qtl /\
               !x. zpfit G x0 (qstepR G x) zp1 /\ zpvalid p0r zp1 /\
                   zpfit G x0 (qstepR G (node_map G x)) zp2 /\
                   zpvalid p0r zp2 /\
                   zpfit G x0 (qstepR G (node_map G (node_map G x))) zp3 /\
                   zpvalid p0r zp3
                   ==> qzt_fitl G x qtl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`zp1:zpart`; `zp2:zpart`; `zp3:zpart`] THEN
  MATCH_MP_TAC quiz_tree_INDUCT THEN
  REWRITE_TAC[red_qzt_leaf; qzt_proper; qzt_fitl] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THENL
   [LEAF_ALL_TAC; LEAF_REC_TAC; LEAF_REC_TAC; LEAF_REC_TAC]);;

let QARITY_OF_NAT_OF_QARITY = prove
 (`!qa. qarity_of_nat (nat_of_qarity qa) = qa`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `qa:qarity` (cases "qarity")) THEN
  REWRITE_TAC[nat_of_qarity; qarity_of_nat] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let QZT_GETR_FIT = prove
 (`!r qt1. qzt_proper (qzt_getr r qt1)
           ==> fitqa r (topqa r) /\ qzt_get1 (topqa r) qt1 = qzt_getr r qt1 /\
           qzt_proper qt1`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `qt1:quiz_tree` (cases "quiz_tree")) THEN
  STRUCT_CASES_TAC(ISPEC `r:prange` (cases "prange")) THEN
  REWRITE_TAC[qzt_getr; qzt_get1; qzt_proper; topqa; fitqa; nat_of_qarity;
              distinctness "prange"; distinctness "qarity";
              ARITH_RULE `5 <= 8 /\ 6 <= 8 /\ 7 <= 8 /\ 8 <= 8`]);;

let REDPART_NO_QZT_FITL = prove
 (`!(G:(A)hypermap) qt y qa1 qa2 qa3.
     (!y. y IN dart G ==> ~qzt_fit G y qt) /\ y IN dart G /\
     arity G y = nat_of_qarity qa1 /\
     arity G (node_map G y) = nat_of_qarity qa2 /\
     arity G (node_map G (node_map G y)) = nat_of_qarity qa3
     ==> ~qzt_fitl G y (qzt_get3 qa1 qa2 qa3 qt)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN
  ASM_REWRITE_TAC[qzt_fit; qzt_fita; LET_DEF; LET_END_DEF;
                  QARITY_OF_NAT_OF_QARITY]);;

(* ------------------------------------------------------------------------- *)
(* The main step: under the section hypotheses one sector of the search      *)
(* fails (Coq NOT_RED_ZPART's body). Generic machinery: each matched leaf    *)
(* gives (RED_QZT_LEAF_FIT) a qzt_fitl at some dart y of the node cycle      *)
(* adjacent to the hub, while the popped ranges force (pop-fit lemmas) the   *)
(* three arities to be the quiz-tree indices, contradicting fit'qt.          *)
(* ------------------------------------------------------------------------- *)

let ZVALID_SHIFTR = prove
 (`!p0r pl pr. 1 < size_part pr /\ zvalid p0r pl pr
               ==> zvalid p0r (shift_part pr pl) (drop_part 1 pr)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p0r:part`; `Zhub`; `Zpart Zhub pl pr`] ZPVALID_SHIFTR) THEN
  ASM_SIMP_TAC[zpvalid; ZSHIFTR_EQ]);;

let ZORG_SHIFT = prove
 (`!(G:(A)hypermap) x0 pl pr.
     0 < size_part pr ==>
     zorg G x0 (shift_part pr pl) = face_map G (zorg G x0 pl)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zorg] THEN
  ASM_SIMP_TAC[SIZE_SHIFT_PART; ITER]);;

let ZORG_CONS = prove
 (`!(G:(A)hypermap) x0 p.
     (!s h. zorg G x0 (Pcons s h p) = face_map G (zorg G x0 p)) /\
     (!h f1. zorg G x0 (Pcons6 h f1 p) = face_map G (zorg G x0 p)) /\
     (!h f1 f2. zorg G x0 (Pcons7 h f1 f2 p) = face_map G (zorg G x0 p)) /\
     (!h f1 f2 f3. zorg G x0 (Pcons8 h f1 f2 f3 p) = face_map G (zorg G x0 p))`
     ,
  REWRITE_TAC[zorg; size_part; ITER]);;

let GET_HAT_CLAUSES = prove
 (`get_hat Pnil = Pr59 /\ (!s h p. get_hat (Pcons s h p) = h) /\
   (!h f1 p. get_hat (Pcons6 h f1 p) = h) /\
   (!h f1 f2 p. get_hat (Pcons7 h f1 f2 p) = h) /\
   (!h f1 f2 f3 p. get_hat (Pcons8 h f1 f2 f3 p) = h)`,
  REWRITE_TAC[get_hat; next_hat]);;

let LEAF_TREE_FOLD = prove
 (`!qa qt r1 r2. qzt_proper (qzt_getr r2 (qzt_getr r1 (qzt_get1 qa qt)))
     ==> fitqa r1 (topqa r1) /\ fitqa r2 (topqa r2) /\
         qzt_getr r2 (qzt_getr r1 (qzt_get1 qa qt)) =
         qzt_get3 qa (topqa r1) (topqa r2) qt`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP QZT_GETR_FIT) THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP QZT_GETR_FIT) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[qzt_get3; qzt_get2]);;

(* The step tactics. Conventions: the hub dart is `zorg G x0 pl`; nhub is    *)
(* written nat_of_qarity ahub throughout (HARGS2).                           *)
let HARGS2 =
 [`G:(A)hypermap`; `nat_of_qarity ahub`; `red_rec:part->bool`;
  `p0r:part`; `x0:A`];;

let is_app_of name tm = let f,_ = strip_comb tm in
is_const f && fst(dest_const f) = name;;
let is_leaf_forall tm =
  is_forall tm &&
  (let b = snd(strip_forall tm) in is_imp b && is_app_of "qzt_fitl" (rand b));;

let GETDEFS =
 [get_spoke; GET_HAT_CLAUSES; get_fan1r; get_fan2r; get_fan3r; get_fan1l;
  get_fan2l; get_fan3l];;

(* Derive `arity <dart> = nat_of_qarity (topqa <range>)` from a pop-fit      *)
(* lemma whenever its fitqa / red_pop preconditions are among the            *)
(* assumptions.                                                              *)
let FACT_TAC lem plt prt rng =
  TRY(MP_TAC(ISPECL (HARGS2 @ [plt; prt; mk_comb(`topqa`, rng)]) lem) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC(GETDEFS @
 [red_popr_spoke; red_pcons; LET_DEF; LET_END_DEF; distinctness "prange"]) THEN
        NO_TAC;
        DISCH_THEN(ASSUME_TAC o REWRITE_RULE GETDEFS)]);;

let DERIVE_FACTS_TAC =
  ASSUM_LIST(fun asl ->
    let zvs = filter (fun th -> is_app_of "zvalid" (concl th)) asl in
    EVERY (map (fun zv ->
      let plt,prt =
  (match snd(strip_comb(concl zv)) with [_;a;b] -> a,b | _ -> failwith "zv") in
      EVERY (map (fun (lem,rng) -> FACT_TAC lem plt prt (rng plt prt))
        [RED_POPR_SPOKE_FIT, (fun pl pr -> mk_comb(`get_spoke`, pr));
         RED_POPL_SPOKE_FIT, (fun pl pr -> mk_comb(`get_spoke`, pl));
         RED_POPR_HAT_FIT, (fun pl pr -> mk_comb(`get_hat`, pr));
         RED_POPL_FAN1R_FIT, (fun pl pr -> mk_comb(`get_fan1r`, pl));
         RED_POPL_FAN2R_FIT, (fun pl pr -> mk_comb(`get_fan2r`, pl));
         RED_POPL_FAN3R_FIT, (fun pl pr -> mk_comb(`get_fan3r`, pl))])) zvs));;

let ZORG_REWR_TAC =
  REWRITE_TAC[zdart; zmove; ZORG_CONS] THEN
  ASSUM_LIST(fun asl ->
    REWRITE_TAC (filter (fun th -> is_eq(concl th) && is_app_of "zorg"
                         (lhs(concl th))) asl));;

(* Close `arity G t = nat_of_qarity q` from an assumption `arity G t' =      *)
(* nat_of_qarity q`.                                                         *)
let ARITY_MATCH_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not(is_app_of "arity" l) then failwith "ARITY_MATCH_TAC" else
    GEN_REWRITE_TAC RAND_CONV [SYM th] THEN ZORG_REWR_TAC THEN
    ((NORM_TAC THEN NO_TAC) ORELSE DFN_TAC));;

let ZPFIT_DIRECT_TAC =
  (REWRITE_TAC[zpfit; zproper; ZPROPER_SHIFTL; distinctness "zpart_loc"] THEN
  NO_TAC) ORELSE
  (REWRITE_TAC[zpfit; zproper; ZPROPER_SHIFTL; distinctness "zpart_loc"] THEN
   ASM_REWRITE_TAC[zdart; zmove; qstepR; qstepL; ZORG_CONS] THEN
   ((NORM_TAC THEN NO_TAC) ORELSE DFN_TAC));;

let ZPVALID_TAC =
  REWRITE_TAC[zpvalid] THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (MATCH_MP_TAC ZPVALID_SHIFTL THEN REWRITE_TAC[zpvalid] THEN
   FIRST_ASSUM ACCEPT_TAC));;

(* Apply the RED_QZT_LEAF_FIT instance to the leaf assumption and fold its   *)
(* tree.                                                                     *)
let LEAF_SETUP_TAC =
  FIRST_ASSUM(fun leaf ->
    if not(is_app_of "red_qzt_leaf" (concl leaf))
    then failwith "LEAF_SETUP_TAC" else
    FIRST_ASSUM(fun lf -> MP_TAC(MATCH_MP lf leaf))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP LEAF_TREE_FOLD) MP_TAC) THEN
  DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (fun eq -> RULE_ASSUM_TAC(REWRITE_RULE[eq]))));;

(* Instantiate the leaf's universal statement at y, discharge the zpfit /    *)
(* zpvalid conditions (zpf closes the proper zpfit goals), then contradict   *)
(* fit'qt via REDPART_NO_QZT_FITL and the derived arity facts.               *)
let FINISH_TAC zpf y =
  FIRST_X_ASSUM(MP_TAC o SPEC y o check (is_leaf_forall o concl)) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (zpf ORELSE ZPVALID_TAC); ALL_TAC] THEN
  REWRITE_TAC[IMP_CLAUSES] THEN MATCH_MP_TAC REDPART_NO_QZT_FITL THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC IN_DART_EQS; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN ARITY_MATCH_TAC;;

(* The t-step variants for the hat-node leaf (Coq's ZDART_STEPRT_ZPART /     *)
(* ZDART_STEPLT_ZPART uses).                                                 *)
let ZPFIT_RT_TAC =
  SUBGOAL_THEN `Zpart (zfanLt pr) (shift_part pr pl) (drop_part 1 pr) =
                zstepRt (rev_part p0r) p0r (Zpart Zhatr pl pr)`
                SUBST1_TAC THENL
   [REWRITE_TAC[zstepRt; zstepRt_loc] THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC ZSHIFTR_EQ THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL (HARGS2 @ [`ahub:qarity`;
                           `Zpart Zhatr pl pr`]) ZDART_STEPRT) THEN
  ASM_REWRITE_TAC[zpvalid; zdart; zmove] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[zpfit_top; zrange; zrange_loc; zdart; zmove] THEN
  ARITY_MATCH_TAC;;

let ZPFIT_LT_TAC =
  SUBGOAL_THEN
 `Zpart (zfanRt pl) pl pr = zstepLt (rev_part p0r) p0r (Zpart Zhatl pl pr)`
 SUBST1_TAC THENL
   [REWRITE_TAC[zstepLt; zstepLt_loc]; ALL_TAC] THEN
  SUBGOAL_THEN
   `qstepR (G:(A)hypermap)
 (node_map G (node_map G (face_map G (node_map G (node_map G
                                                  (zorg G x0 pl)))))) =
    qstepL G (zdart G x0 (Zpart Zhatl pl pr))` SUBST1_TAC THENL
   [REWRITE_TAC[zdart; zmove; qstepL; qstepR] THEN NORM_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL (HARGS2 @ [`ahub:qarity`;
                           `Zpart Zhatl pl pr`]) ZDART_STEPLT) THEN
  ASM_REWRITE_TAC[zpvalid] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[zpfit_top; zrange; zrange_loc; zdart; zmove] THEN
  ARITY_MATCH_TAC;;

let ZPFIT_T_TAC = ZPFIT_DIRECT_TAC ORELSE ZPFIT_RT_TAC ORELSE ZPFIT_LT_TAC;;

(* The per-sector alternatives (red_zpart_cases): the leaf dart is f^k (e x) *)
(* for k = 3..6; try them all.                                               *)
let yk k =
  list_mk_comb(`ITER:num->(A->A)->A->A`,
               [mk_small_numeral k; `face_map (G:(A)hypermap)`;
                `edge_map (G:(A)hypermap) (zorg G x0 pl)`]);;

let ALT_TAC =
  LEAF_SETUP_TAC THEN STRIP_TAC THEN DERIVE_FACTS_TAC THEN
  FIRST (map (fun k -> FINISH_TAC ZPFIT_DIRECT_TAC (yk k)) [3;4;5;6]);;

let CASE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE GETDEFS) THEN REWRITE_TAC GETDEFS THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check
        (fun th -> lhs(concl th) = `a0:prange`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[mem_range])) THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[] THEN TRY ALT_TAC);;

let NOT_RED_ZPART_STEP = prove
 (`!(G:(A)hypermap) red_rec p0r x0 ahub qt pl pr.
     redpart_hyps G (nat_of_qarity ahub) red_rec p0r x0 /\
     (!y. y IN dart G ==> ~qzt_fit G y qt) /\ zvalid p0r pl pr /\
     1 < size_part pr
     ==> ~red_zpart_step red_rec (nat_of_qarity ahub) ahub qt (rev_part p0r)
     p0r (Zpart Zhub pl pr)
            (Zpart Zhub (shift_part pr pl) (drop_part 1 pr))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[redpart_hyps; plain_cubic_pentagonal; plain_cubic] o
              check (fun th -> is_app_of "redpart_hyps" (concl th))) THEN
  SUBGOAL_THEN `zvalid p0r (shift_part pr pl) (drop_part 1 pr)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ZVALID_SHIFTR]; ALL_TAC] THEN
  SUBGOAL_THEN `zorg G x0 (shift_part pr pl) = face_map G (zorg G x0 pl:A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ZORG_SHIFT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
 `!zj zk. zdart (G:(A)hypermap) x0
  (zshiftl (rev_part p0r) p0r zj (Zpart zk pl pr)) =
                        zmove zj G (edge_map G (node_map G (zorg G x0 pl)))`
                        ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL
      [`G:(A)hypermap`; `x0:A`; `rev_part p0r`; `p0r:part`; `zj:zpart_loc`;
                   `Zpart zk pl pr`] ZDART_SHIFTL) THEN
    ASM_REWRITE_TAC[plain_cubic_pentagonal; plain_cubic;
                    SIZE_REV_PART; zporg] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  SUBGOAL_THEN `arity G (zorg G x0 pl:A) = nat_of_qarity ahub` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[zorg; ARITY_ITER_FACE_GEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(zorg G x0 pl:A) IN dart G` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[zorg; ITER_FACE_IN_DART_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `fitp pr G (zorg G x0 pl:A)` ASSUME_TAC THENL
  [ASM_MESON_TAC[ZVALID_FITR]; ALL_TAC] THEN
  MP_TAC(ISPECL (HARGS2 @ [`ahub:qarity`]) RED_QZT_LEAF_FIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[red_zpart_step; zp_pl; zp_pr; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP QZT_GETR_FIT o check
    (fun th -> is_app_of "qzt_proper" (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))
    THEN
  DISCH_THEN(fun eq ->
    MP_TAC(ISPECL [`topqa (get_spoke pr)`;
                   `qt:quiz_tree`] QZT_GET1_TRUNCATE) THEN
    ASM_REWRITE_TAC[eq] THEN DISCH_THEN(fun eq2 -> REWRITE_TAC[eq2])) THEN
  COND_CASES_TAC THENL
   [LEAF_SETUP_TAC THEN STRIP_TAC THEN DERIVE_FACTS_TAC THEN
    FINISH_TAC ZPFIT_DIRECT_TAC `zorg (G:(A)hypermap) x0 pl`;
    COND_CASES_TAC THENL
     [LEAF_SETUP_TAC THEN STRIP_TAC THEN DERIVE_FACTS_TAC THEN
      FINISH_TAC ZPFIT_T_TAC
        `face_map (G:(A)hypermap) (node_map G (node_map G (zorg G x0 pl)))`;
      UNDISCH_TAC `fitp pr (G:(A)hypermap) (zorg G x0 pl)` THEN
      MP_TAC(ISPEC `pr:part` (cases "part")) THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `pr:part`
      )) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[shift_part; ONE; take_part; cat_part;
                                  drop_part]) THEN
      REWRITE_TAC[red_zpart_cases; shift_part; ONE; take_part; cat_part;
                  drop_part; fitp;
                  subpart_loc_move; mem_range] THEN
      STRIP_TAC THEN CASE_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Coq NOT_RED_ZPART (the induction over the nhub right shifts), then the    *)
(* two exported theorems.                                                    *)
(* ------------------------------------------------------------------------- *)

let NOT_RED_ZPART_REC = prove
 (`!(G:(A)hypermap) red_rec p0r x0 ahub qt.
     redpart_hyps G (nat_of_qarity ahub) red_rec p0r x0 /\
     (!y. y IN dart G ==> ~qzt_fit G y qt)
     ==> !d pl pr. d < size_part pr /\ zvalid p0r pl pr
                  ==> ~red_zpart_rec red_rec (nat_of_qarity ahub) ahub qt
                  (rev_part p0r) p0r d
                        (Zpart Zhub pl pr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[red_zpart_rec] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 < size_part pr` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
         [`rev_part p0r`; `p0r:part`; `Zhub`; `Zhub`; `pl:part`; `pr:part`]
         ZSHIFTR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `red_rec:part->bool`; `p0r:part`; `x0:A`;
                   `ahub:qarity`; `qt:quiz_tree`; `pl:part`; `pr:part`]
           NOT_RED_ZPART_STEP) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SIZE_DROP_PART] THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[ZVALID_SHIFTR]]]);;

(* Coq NOT_RED_ZPART (Section RedpartRec): under the section hypotheses the  *)
(* one-step search returns false.                                            *)
let NOT_RED_ZPART = prove
 (`!(G:(A)hypermap) qt ahub (red_rec:part->bool) p0r x0.
     plain_cubic_pentagonal G /\
     (!y. y IN dart G ==> ~qzt_fit G y qt) /\
     (!x p. x IN dart G /\ arity G x = nat_of_qarity ahub /\
     exact_fitp G x p ==> ~red_rec p) /\
     x0 IN dart G /\ exact_fitp G x0 p0r /\ arity G x0 = nat_of_qarity ahub
     ==> ~red_zpart red_rec ahub qt (rev_part p0r) p0r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[red_zpart] THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `red_rec:part->bool`; `p0r:part`; `x0:A`;
                 `ahub:qarity`; `qt:quiz_tree`] NOT_RED_ZPART_REC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[redpart_hyps]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ZVALID_INITL] THEN
  SUBGOAL_THEN `size_part p0r = nat_of_qarity ahub` ASSUME_TAC THENL
   [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rev_part p0r`; `p0r:part`] SIZE_SHIFT_PART) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SIZE_REV_PART] THEN
    ASM_MESON_TAC[ARITY_POS_PENTA; plain_cubic_pentagonal];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let NO_FIT_REDPART_LOOP = prove
 (`!(G:(A)hypermap) qt. plain_cubic_pentagonal G /\
 (!y. y IN dart G ==> ~qzt_fit G y qt)
     ==> !d ahub p x. size_part p = nat_of_qarity ahub /\ x IN dart G /\
     exact_fitp G x p
                      ==> ~redpart_loop qt ahub d p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[redpart_loop] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `qt:quiz_tree`; `ahub:qarity`;
                 `redpart_loop qt ahub d`; `p:part`; `x:A`] NOT_RED_ZPART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `x1:A` THEN X_GEN_TAC `p1:part` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ahub:qarity`; `p1:part`; `x1:A`]) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[exact_fitp]; DISCH_THEN ACCEPT_TAC];
    ASM_MESON_TAC[exact_fitp]]);;

(* Coq NO_FIT_REDPART.                                                       *)
let NO_FIT_REDPART = prove
 (`!(G:(A)hypermap) qt p.
     plain_cubic_pentagonal G /\ (!y. y IN dart G ==> ~qzt_fit G y qt) /\
     redpart qt p
     ==> !x. x IN dart G ==> ~exact_fitp G x p`,
  REWRITE_TAC[redpart; LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `qt:quiz_tree`] NO_FIT_REDPART_LOOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`size_part p * 12`; `qarity_of_nat (size_part p)`;
                             `p:part`; `x:A`]) THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC);;

