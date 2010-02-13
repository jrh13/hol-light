
let AND_IMP = prove
  (`!a b c. a /\ b ==> c <=> a ==> b ==> c`,CONV_TAC TAUT);;
let AND_IMP2 = prove
  (`!a b c. a /\ b ==> c <=> (a<=>T) ==> b ==> c`,CONV_TAC TAUT);;
let AND_IMP3 = prove
  (`!a b c. ~a /\ b ==> c <=> (a<=>F) ==> b ==> c`,CONV_TAC TAUT);;
 
let NOT_NOT = GEN_ALL (hd (CONJUNCTS (SPEC_ALL NOT_CLAUSES)));;

let AND_INV = prove
  (`!a. (~a /\ a) <=> F`,CONV_TAC TAUT);;

let AND_INV_IMP = prove
  (`!a. a ==> ~a ==> F`,CONV_TAC TAUT);;
 
let OR_DUAL = prove
  (`(~(a \/ b) ==> F) = (~a ==> ~b ==> F)`,CONV_TAC TAUT);; 

let OR_DUAL2 = prove
  (`(~(a \/ b) ==> F) = ((a==>F) ==> ~b ==> F)`,CONV_TAC TAUT);; 

let OR_DUAL3 = prove
  (`(~(~a \/ b) ==> F) = (a ==> ~b ==> F)`,CONV_TAC TAUT);; 

let AND_INV2 = prove
  (`(~a ==> F) ==> (a==>F) ==> F`,CONV_TAC TAUT)

let NOT_ELIM2 = prove
(`(~a ==> F) <=> a`,CONV_TAC TAUT)

let IMP_F_EQ_F = prove
  (`!t. (t ==> F) <=> (t <=> F)`,CONV_TAC TAUT);;
