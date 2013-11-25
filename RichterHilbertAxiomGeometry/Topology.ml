(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* An in-progress readable.ml port of the point-set topology in              *)
(* Multivariate/topology.ml.                                                 *)

needs "RichterHilbertAxiomGeometry/readable.ml";;

let DIFF_UNION = prove
 (`!u s t. u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)`,
  SET_TAC[]);;

let DIFF_REFL = prove
 (`!u t. t SUBSET u ==> u DIFF (u DIFF t) = t`,
  SET_TAC[]);;

let INTERS_SUBSET = prove
 (`!f t. ~(f = {}) /\ (!s. s IN f ==> s SUBSET t) ==> INTERS f SUBSET t`,
  SET_TAC[]);;

let IN_SET_FUNCTION_PREDICATE = prove
 (`!x f P. x IN {f y | P y} <=> ?y. x = f y /\ P y`,
  SET_TAC[]);;


ParseAsInfix("∉",(11, "right"));;

let NOTIN = NewDefinition `;
  ∀a l. a ∉ l ⇔ ¬(a ∈ l)`;;

let istopology = NewDefinition `;
  istopology (X, L)  ⇔
  (∀U. U ∈ L  ⇒  U ⊂ X)  ∧  ∅ ∈ L  ∧  X ∈ L  ∧
  (∀s t. s ∈ L ∧ t ∈ L  ⇒ s ∩ t ∈ L)  ∧ ∀k. k ⊂ L  ⇒  UNIONS k IN L`;;

let UnderlyingSpace = NewDefinition `;
  UnderlyingSpace α = FST α`;;

let OpenSets = NewDefinition `;
  OpenSets α = SND α`;;

let ExistsTopology = theorem `;
  ∀X. ∃α. istopology α  ∧  UnderlyingSpace α = X

  proof
    intro_TAC ∀X;
    consider L such that L = {U | U ⊂ X}     [Lexists] by fol;
    exists_TAC (X, L);
    rewrite istopology IN_ELIM_THM Lexists UnderlyingSpace;
    set;
  qed;
`;;

let topology_tybij_th = theorem `;
  ?t. istopology t
  by fol ExistsTopology`;;

let topology_tybij =
  new_type_definition "topology" ("mk_topology","dest_topology")
  topology_tybij_th;;

let ISTOPOLOGYdest_topology = theorem `;
  ∀α. istopology (dest_topology α)
  by fol topology_tybij`;;

let open_in = NewDefinition `;
  ∀α. open_in α = OpenSets (dest_topology α)`;;

let topspace = NewDefinition `;
  ∀α. topspace α = UnderlyingSpace (dest_topology  α)`;;

let TopologyPAIR = theorem `;
  ∀α.  dest_topology α = (topspace α, open_in α)
  by rewrite PAIR_EQ open_in topspace UnderlyingSpace OpenSets`;;

let Topology_Eq = theorem `;
  ∀α β.  topspace α =  topspace β  ∧  (∀U. open_in α U ⇔ open_in β U)
    ⇔ α = β

  proof
    intro_TAC ∀α β;
    eq_tac [Right]     by fol;
    intro_TAC H1 H2;
    dest_topology α = dest_topology β     [] by simplify TopologyPAIR PAIR_EQ H1 H2 FUN_EQ_THM;
    fol - topology_tybij;
  qed;
`;;

let OpenInCLAUSES = theorem `;
  ∀α X. topspace α = X  ⇒
    (∀U. open_in α U  ⇒  U ⊂ X)  ∧  open_in α ∅  ∧  open_in α X  ∧
    (∀s t. open_in α s ∧ open_in α t  ⇒ open_in α (s ∩ t))  ∧
    ∀k. (∀s. s ∈ k ⇒ open_in α s)  ⇒  open_in α (UNIONS k)

  proof
    intro_TAC ∀α X, H1;
    consider L such that L = open_in α     [Ldef] by fol;
    istopology (X, L)     [] by fol H1 Ldef TopologyPAIR PAIR_EQ ISTOPOLOGYdest_topology;
    fol Ldef - istopology IN SUBSET;
  qed;
`;;

let OpenInSubset = theorem `;
  ∀α s.  open_in α s  ⇒  s ⊂ topspace α
  by fol OpenInCLAUSES`;;

let OpenInEmpty = theorem `;
  ∀α. open_in α ∅
  by fol OpenInCLAUSES`;;

let OpenInInter = theorem `;
  ∀α s t. open_in α s ∧ open_in α t  ⇒  open_in α (s ∩ t)
  by fol OpenInCLAUSES`;;

let OpenInUnions = theorem `;
  ∀α k. (∀s. s ∈ k ⇒ open_in α s)  ⇒  open_in α (UNIONS k)
  by fol OpenInCLAUSES`;;

let OpenInUnderlyingSpace = theorem `;
  ∀α X. topspace α = X  ⇒  open_in α X
  by fol OpenInCLAUSES`;;

let OpenInUnion = theorem `;
  ∀α s t. open_in α s ∧ open_in α t  ⇒  open_in α (s ∪ t)

  proof
    intro_TAC ∀α s t, H;
    ∀x. x ∈ {s, t} ⇔ x = s ∨ x = t     [] by fol IN_INSERT NOT_IN_EMPTY;
    fol - UNIONS_2 H OpenInUnions;
  qed;
`;;

let OpenInTopspace = theorem `;
  ∀α. open_in α (topspace α)
  by fol OpenInCLAUSES`;;

let OpenInInters = theorem `;
  ∀α s. FINITE s ∧ ¬(s = ∅) ∧ (∀t. t ∈ s ⇒ open_in α t)
    ⇒ open_in α (INTERS s)

  proof
    intro_TAC ∀α;
    rewrite IMP_CONJ;
    MATCH_MP_TAC FINITE_INDUCT;
    rewrite INTERS_INSERT NOT_INSERT_EMPTY FORALL_IN_INSERT;
      intro_TAC ∀x s, H1, xWorks sWorks;
    case_split Empty | Nonempty     by fol;
    suppose s = ∅;
      rewrite Empty INTERS_0 INTER_UNIV xWorks;
    end;
    suppose ¬(s = ∅);
      open_in alpha (INTERS s)     [] by fol Nonempty H1 sWorks;
      fol xWorks - OpenInInter;
    end;
  qed;
`;;

let OpenInSubopen = theorem `;
  ∀α s.  open_in α s ⇔ ∀x. x ∈ s ⇒ ∃t. open_in α t ∧ x ∈ t ∧ t ⊂ s

  proof
    intro_TAC ∀α s;
    eq_tac [Left]     by fol SUBSET_REFL;
    intro_TAC H1;
    consider f such that
    ∀x. x ∈ s  ⇒  open_in α (f x) ∧ x ∈ f x ∧ f x ⊂ s     [fExists] by fol H1 SKOLEM_THM_GEN;
    consider s1 such that s1 = UNIONS (IMAGE f s)     [s1Def] by fol;
    open_in α s1     [s1open] by fol s1Def fExists fExists GSYM FORALL_IN_IMAGE OpenInUnions;
    s = s1     [] by set s1Def fExists;
    fol s1open -;
  qed;
`;;

let closed_in = NewDefinition `;
  ∀α s. closed_in α s  ⇔  ∃X. X = topspace α ∧
      s ⊂ X ∧ open_in α (X ◼ s)`;;

let USEclosed_in = theorem `;
  ∀α s X. X = topspace α  ⇒
    (closed_in α s  ⇔  s ⊂ X ∧ open_in α (X ◼ s))
  by fol closed_in`;;

let ClosedInSubset  = theorem `;
  ∀α s. closed_in α s   ⇒  s ⊂ topspace α
  by fol closed_in`;;

let ClosedInEmpty = theorem `;
  ∀α. closed_in α ∅
  by fol closed_in EMPTY_SUBSET DIFF_EMPTY OpenInTopspace`;;

let ClosedInTopspace = theorem `;
  ∀α. closed_in α (topspace α)
  by fol closed_in SUBSET_REFL DIFF_EQ_EMPTY OpenInEmpty`;;

let ClosedInUnion = theorem `;
  ∀α s t. closed_in α s ∧ closed_in α t  ⇒  closed_in α (s ∪ t)

  proof
    intro_TAC ∀α s t, Hst;
    consider X such that X = topspace α     [Xdef] by fol;
    fol Hst Xdef USEclosed_in DIFF_UNION UNION_SUBSET OpenInInter;
  qed;
`;;

let ClosedInInters = theorem `;
  ∀α k.  ¬(k = ∅) ∧ (∀s. s ∈ k ⇒ closed_in α s)  ⇒  closed_in α (INTERS k)

  proof
    intro_TAC ∀α k, H1 H2;
    consider X such that X = topspace α     [Xdef] by fol;
    simplify GSYM Xdef USEclosed_in DIFF_INTERS SIMPLE_IMAGE;
    fol H1 H2 Xdef INTERS_SUBSET USEclosed_in FORALL_IN_IMAGE OpenInUnions;
  qed;
`;;

let ClosedInInter = theorem `;
  ∀α s t. closed_in α s ∧ closed_in α t ⇒ closed_in α (s ∩ t)

  proof
    intro_TAC ∀α s t, Hs Ht;
    rewrite GSYM INTERS_2;
    MATCH_MP_TAC ClosedInInters;
    set Hs Ht;
  qed;
`;;

let OpenInClosedInEq = theorem `;
  ∀α X s. X = topspace α  ⇒
    (open_in α s  ⇔  s ⊂ X ∧ closed_in α (X ◼ s))

  proof
    intro_TAC ∀α X s, Xdef;
    simplify Xdef USEclosed_in SUBSET_DIFF OpenInSubset;
    fol Xdef SET_RULE [X ◼ (X ◼ s) = X ∩ s  ∧  (s ⊂ X ⇒ X ∩ s = s)] OpenInSubset;
  qed;
`;;

let OpenInClosedIn = theorem `;
  ∀s X. X = topspace α  ∧  s ⊂ X
    ⇒ (open_in α s ⇔ closed_in α (X ◼ s))
  by fol OpenInClosedInEq`;;


let OpenInDiff = theorem `;
  ∀α s t.  open_in α s ∧ closed_in α t  ⇒  open_in α (s ◼ t)

  proof
    intro_TAC ∀α s t, H1 H2;
    consider X such that X = topspace α     [Xdef] by fol;
    s ⊂ X  ∧  t ⊂ X [] by fol Xdef H1 OpenInSubset H2 USEclosed_in;
    s ◼ t = s ∩ (X ◼ t) [] by set -;
    fol - Xdef H1 H2 USEclosed_in OpenInInter;
  qed;
`;;

let ClosedInDiff = theorem `;
  ∀α s t.  closed_in α s ∧ open_in α t  ⇒  closed_in α (s ◼ t)

  proof
    intro_TAC ∀α s t, H1 H2;
    consider X such that X = topspace α     [Xdef] by fol;
    s ⊂ X  ∧  t ⊂ X [stX] by fol Xdef H1 USEclosed_in H2 OpenInSubset;
    s ◼ t = s ∩ (X ◼ t) [] by set -;
    fol - H1 Xdef stX SUBSET_DIFF DIFF_REFL H2 USEclosed_in ClosedInInter;
  qed;
`;;

let ClosedInUnions = theorem `;
  ∀α s.  FINITE s ∧ (∀t. t ∈ s ⇒ closed_in α t)
    ⇒ closed_in α (UNIONS s)

  proof
    intro_TAC ∀α;
    rewrite IMP_CONJ;
    MATCH_MP_TAC FINITE_INDUCT;
    fol UNIONS_INSERT UNIONS_0 ClosedInEmpty IN_INSERT ClosedInUnion;
  qed;
`;;

let subtopology = NewDefinition `;
  ∀α u.  subtopology α u = mk_topology (u, {s ∩ u | open_in α s})`;;

let IstoplogySubtopology_PROCEDURAL = theorem `;
  ∀α u:A->bool. u ⊂ topspace α  ⇒  istopology (u, {s ∩ u | open_in α s})

  proof
    intro_TAC ∀α u, H1;
    simplify istopology IN_SET_FUNCTION_PREDICATE LEFT_IMP_EXISTS_THM INTER_SUBSET GSYM LEFT_EXISTS_AND_THM;
    exists_TAC ∅:A->bool;
    conj_tac [Left]     by fol INTER_EMPTY OpenInEmpty;
    exists_TAC topspace α;
    conj_tac [Left]     by fol OpenInTopspace H1 INTER_COMM SUBSET_INTER_ABSORPTION;
    conj_tac [Left]     by fol SET_RULE [(s' ∩ u) ∩ (s ∩ u) = (s ∩ s') ∩ u] OpenInInter;
    rewrite SET_RULE [{s ∩ u | open_in α s} =IMAGE (λs. s ∩ u) {s | open_in α s}] FORALL_SUBSET_IMAGE;
    intro_TAC ∀k, kProp;
    exists_TAC UNIONS k;
    ∀y. y ∈ k  ⇒ open_in alpha y     [] by set kProp;
    open_in alpha (UNIONS k)     [] by fol - OpenInUnions;
    simplify - UNIONS_IMAGE UNIONS_GSPEC INTER_UNIONS;
  qed;
`;;

let IstoplogySubtopology = theorem `;
  ∀α u:A->bool. u ⊂ topspace α  ⇒  istopology (u, {s ∩ u | open_in α s})

  proof
    intro_TAC ∀α u, H1;
    ∅ = ∅ ∩ u ∧ open_in α ∅     [emptysetOpen] by fol INTER_EMPTY OpenInEmpty;
    u = topspace α ∩ u ∧ open_in α (topspace α)     [uOpen] by fol OpenInTopspace H1 INTER_COMM SUBSET_INTER_ABSORPTION;
    ∀s' s. open_in α s' ∧ open_in α s  ⇒  open_in α (s' ∩ s)  ∧
    (s' ∩ u) ∩ (s ∩ u) = (s' ∩ s) ∩ u   [interOpen]
    proof
      intro_TAC ∀s' s, H1 H2;
      open_in α (s' ∩ s)     [] by fol H1 H2 OpenInInter;
      set -;
    qed;
    ∀k. k ⊂ {s | open_in α s}  ⇒  open_in α (UNIONS k)  ∧
    UNIONS (IMAGE (λs. s ∩ u) k) = (UNIONS k) ∩ u  [unionsOpen]
    proof
      intro_TAC ∀k, kProp;
      ∀y. y ∈ k  ⇒ open_in α y     [kOpen] by set kProp;
      open_in α (UNIONS k)     [] by fol kOpen OpenInUnions;
      simplify - UNIONS_IMAGE UNIONS_GSPEC INTER_UNIONS;
    qed;
    {s ∩ u | open_in α s} = IMAGE (λs. s ∩ u) {s | open_in α s}     [] by set;
    simplify istopology IN_SET_FUNCTION_PREDICATE LEFT_IMP_EXISTS_THM INTER_SUBSET - FORALL_SUBSET_IMAGE;
    fol  emptysetOpen uOpen interOpen unionsOpen;
  qed;
`;;

let OpenInSubtopology = theorem `;
  ∀α u s. u ⊂ topspace α ⇒
    (open_in (subtopology α u) s ⇔ ∃t. open_in α t ∧ s = t ∩ u)

  proof
    intro_TAC ∀α u s, H1;
    open_in (subtopology α u) = OpenSets (u,{s ∩ u | open_in α s})     [] by fol subtopology H1 IstoplogySubtopology topology_tybij open_in;
    rewrite - OpenSets PAIR_EQ SND EXTENSION IN_ELIM_THM;
  qed;
`;;

let TopspaceSubtopology = theorem `;
  ∀α u. u ⊂ topspace α  ⇒  topspace (subtopology α u) = u

  proof
    intro_TAC ∀α u , H1;
    topspace (subtopology α u) = UnderlyingSpace (u,{s ∩ u | open_in α s})     [] by fol subtopology H1 IstoplogySubtopology topology_tybij topspace;
    rewrite - UnderlyingSpace PAIR_EQ FST;
    fol  INTER_COMM H1 SUBSET_INTER_ABSORPTION;
  qed;
`;;

let ClosedInSubtopology = theorem `;
  ∀α u C.  u ⊂ topspace α  ⇒
    (closed_in (subtopology α u) C  ⇔  ∃D. closed_in α D ∧ C = D ∩ u)

  proof
    intro_TAC ∀α u C, H1;
    consider X such that
    X = topspace α ∧ u ⊂ X     [Xdef] by fol H1;
    closed_in (subtopology α u) C  ⇔
    ∃t. C ⊂ u ∧ t ⊂ X ∧ open_in α t ∧ u ◼ C = t ∩ u     [] by fol USEclosed_in H1 Xdef OpenInSubtopology OpenInSubset TopspaceSubtopology;
    closed_in (subtopology α u) C  ⇔
    ∃D. C ⊂ u ∧ D ⊂ X ∧ open_in α (X ◼ D) ∧ u ◼ C = (X ◼ D) ∩ u     []
    proof
      rewrite -;
      eq_tac [Left]
      proof
        STRIP_TAC;     exists_TAC X ◼ t;
        ASM_SIMP_TAC H1 Xdef OpenInSubset DIFF_REFL SUBSET_DIFF;
      qed;
      STRIP_TAC;     exists_TAC X ◼ D;
      ASM_SIMP_TAC SUBSET_DIFF;
    qed;
    simplify - GSYM Xdef H1 USEclosed_in;
    ∀D C. C ⊂ u ∧ u ◼ C = (X ◼ D) ∩ u  ⇔  C = D ∩ u     [] by set Xdef DIFF_REFL INTER_SUBSET;
    fol -;
  qed;
`;;

let OpenInSubtopologyEmpty = theorem `;
  ∀α s. open_in (subtopology α ∅) s ⇔ s = ∅

  proof
    simplify EMPTY_SUBSET OpenInSubtopology INTER_EMPTY;
    fol  OpenInEmpty;
  qed;
`;;

let ClosedInSubtopologyEmpty = theorem `;
  ∀α s. closed_in (subtopology α ∅) s ⇔ s = ∅

  proof
    simplify EMPTY_SUBSET ClosedInSubtopology INTER_EMPTY;
    fol  ClosedInEmpty;
  qed;
`;;

let SubtopologyTopspace = theorem `;
  ∀α. subtopology α (topspace α) = α

  proof
    intro_TAC ∀α;
    topspace α ⊂ topspace α [Xsubset] by fol SUBSET_REFL;
    topspace (subtopology α (topspace α)) = topspace α [topXsub] by fol Xsubset TopspaceSubtopology;
    simplify topXsub GSYM Topology_Eq;
    fol Xsubset OpenInSubtopology OpenInSubset SUBSET_INTER_ABSORPTION;
  qed;
`;;
