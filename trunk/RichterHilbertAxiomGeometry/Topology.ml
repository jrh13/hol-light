(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* An in-progress readable.ml port of the point-set topology in              *)
(* Multivariate/topology.ml.						     *)

needs "RichterHilbertAxiomGeometry/readable.ml";;

ParseAsInfix("∉",(11, "right"));;

let NOTIN = NewDefinition `;
  ∀a l. a ∉ l ⇔ ¬(a ∈ l)`;;

let istopology = NewDefinition `;
  istopology X L  ⇔ 
  (∀U. U ∈ L  ⇒  U ⊂ X)  ∧  ∅ ∈ L  ∧  X ∈ L  ∧
  (∀s t. s ∈ L ∧ t ∈ L  ⇒ s ∩ t ∈ L)  ∧ ∀k. k ⊂ L  ⇒  UNIONS k IN L`;;

let TopSpace = NewDefinition `;
  TopSpace α  ⇔ ∃X L. α = (X, L)  ∧ istopology X L`;;

let UnderlyingSpace = NewDefinition `;
  UnderlyingSpace α = FST α`;;

let OpenSets = NewDefinition `;
  OpenSets α = SND α`;;

let makeTopSpace = NewDefinition `;
  ∀X L. makeTopSpace X L = (X, L)`;;

let open_in = NewDefinition `;
  ∀α U. open_in α U ⇔ U ∈ OpenSets α`;;

let toMakeTopSpace = theorem `;
  ∀X L α. α = makeTopSpace X L ∧ istopology X L
    ⇒ TopSpace α ∧ UnderlyingSpace α = X ∧ OpenSets α = L

  proof
    intro_TAC ∀ X L;
    rewrite FORALL_PAIR_THM UnderlyingSpace OpenSets TopSpace makeTopSpace  PAIR_EQ FST SND;
    fol;
  qed;
`;;

let ExistsTopology = theorem `;
  ∀X. ∃α. TopSpace α  ∧  UnderlyingSpace α = X

  proof
    intro_TAC ∀ X;
    consider L such that L = {U | U ⊂ X} [Lexists] by fol;
    consider α such that α = makeTopSpace X L [αexists] by fol;
    istopology X L [istopologyXL] 
    proof     rewrite istopology IN_ELIM_THM Lexists;     set;     qed;
    fol αexists - toMakeTopSpace;
  qed;
`;;

let Topology_Eq = theorem `;
  ∀α β. TopSpace α ∧ TopSpace β ∧ 
    UnderlyingSpace α = UnderlyingSpace β ∧ 
    (∀U. open_in α U ⇔ open_in β U)
    ⇒ α = β

  proof
    rewrite FORALL_PAIR_THM UnderlyingSpace OpenSets TopSpace makeTopSpace open_in PAIR_EQ FST SND;
    simplify GSYM FUN_EQ_THM IN ETA_AX;
  qed;
`;;

let OpenInCLAUSES = theorem `;
  ∀α X. TopSpace α ∧  UnderlyingSpace α = X  ⇒ 
    (∀U. open_in α U  ⇒  U ⊂ X)  ∧  open_in α ∅  ∧  open_in α X  ∧
    (∀s t. open_in α s ∧ open_in α t  ⇒ open_in α (s ∩ t))  ∧ 
    ∀k. (∀s. s ∈ k ⇒ open_in α s)  ⇒  open_in α (UNIONS k)

  proof
    rewrite FORALL_PAIR_THM UnderlyingSpace OpenSets TopSpace istopology open_in PAIR_EQ FST SND SUBSET;
    fol;
  qed;
`;;

let OpenInClauses = theorem `;
  ∀α. TopSpace α  ⇒ 
    open_in α ∅ ∧
    (∀s t. open_in α s ∧ open_in α t  ⇒  open_in α (s ∩ t)) ∧
    (∀k. (∀s. s ∈ k ⇒ open_in α s)  ⇒  open_in α (UNIONS k))
  by fol OpenInCLAUSES`;;

let OpenInSubset = theorem `;
  ∀α s X. TopSpace α ∧ open_in α s ∧ UnderlyingSpace α = X
    ⇒ s ⊂ X
  by fol OpenInCLAUSES`;;

let OpenInEmpty = theorem `;
  ∀α. TopSpace α  ⇒  open_in α ∅
  by fol OpenInCLAUSES`;;

let OpenInInter = theorem `;
  ∀α s t. TopSpace α ∧ open_in α s ∧ open_in α t  ⇒  open_in α (s ∩ t)
  by fol OpenInCLAUSES`;;

let OpenInUnions = theorem `;
  ∀α k. TopSpace α ∧ (∀s. s ∈ k ⇒ open_in α s)  ⇒  open_in α (UNIONS k)
  by fol OpenInCLAUSES`;;

let OpenInUnderlyingSpace = theorem `;
  ∀α X. TopSpace α ∧  UnderlyingSpace α = X  ⇒  open_in α X
  by fol OpenInCLAUSES`;;

let OpenInUnion = theorem `;
  ∀α s t. TopSpace α ∧ open_in α s ∧ open_in α t  ⇒  open_in α (s ∪ t)

  proof
    intro_TAC ∀α s t, H;
    ∀x. x ∈ {s, t} ⇔ x = s ∨ x = t [] by fol IN_INSERT NOT_IN_EMPTY;
    fol - UNIONS_2 H OpenInUnions;
  qed;
`;;

let OpenInInters = theorem `;
  ∀α s. FINITE s ∧ TopSpace α ∧ ¬(s = ∅) ∧ (∀t. t ∈ s ⇒ open_in α t)
    ⇒ open_in α (INTERS s)

  proof
    intro_TAC ∀α;
    rewrite IMP_CONJ;
    MATCH_MP_TAC FINITE_INDUCT;
    rewrite INTERS_INSERT NOT_INSERT_EMPTY FORALL_IN_INSERT;
      intro_TAC ∀x s, H1, Topα, xWorks sWorks;
    case_split Empty | Nonempty     by fol;
    suppose s = ∅;
      rewrite Empty INTERS_0 INTER_UNIV xWorks;
    end;
    suppose ¬(s = ∅);
      open_in alpha (INTERS s) [] by fol Topα Nonempty H1 sWorks;
      fol Topα xWorks - OpenInInter;
    end;
  qed;
`;;

let OpenInSubopen = theorem `;
  ∀α s.  TopSpace α   ⇒  
    (open_in α s ⇔ ∀x. x ∈ s ⇒ ∃t. open_in α t ∧ x ∈ t ∧ t ⊂ s)

  proof
    intro_TAC ∀α s, Topα;
    simplify SUBSET_REFL;
    open_in α s  ⇒  ∀x. x ∈ s ⇒ ∃t. open_in α t ∧ x ∈ t ∧ t ⊂ s     [LeftImp] by fol SUBSET_REFL;
    (∀x. x ∈ s ⇒ ∃t. open_in α t ∧ x ∈ t ∧ t ⊂ s)  ⇒  open_in α s     [] 
    proof
      intro_TAC H1;
      consider f such that 
      ∀x. x ∈ s  ⇒  open_in α (f x) ∧ x ∈ f x ∧ f x ⊂ s     [fExists] by fol H1 AXIOM_OF_CHOICE_read;
      consider s1 such that s1 = UNIONS (IMAGE f s)     [s1Def] by fol;
      open_in α s1     [s1open] by fol s1Def fExists fExists GSYM FORALL_IN_IMAGE Topα OpenInUnions;
      s = s1     [] by set s1Def fExists;
      fol s1open -;
    qed;
    fol LeftImp -;
  qed;
`;;
