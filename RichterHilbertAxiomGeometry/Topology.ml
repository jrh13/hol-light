(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* An ongoing readable.ml port of Multivariate/topology.ml with 3 features:  *)
(* 1) A topological space will be an ordered pair α = (X, L), where L is the *)
(* the set of open sets on X.  topology.ml defines a topological space to be *)
(* just L, and the topspace X is defined as UNIONS L.                        *)
(* 2) Result about Connectiveness, limit points, interior and closure  are   *)
(* first proved for general topological spaces and then specialized to       *)
(* Euclidean space.                                                          *)
(* 3)All general topology theorems using subtopology α u have antecedent     *)
(* u ⊂ topspace α.                                                           *)
(* The math character ━ is used for DIFF.                                    *)
(* This file, together with from_topology.ml, shows that all 18965 lines of  *)
(* Multivariate/topology.ml are either ported/modified here, or else run on  *)
(* top of this file.                                                         *)

needs "RichterHilbertAxiomGeometry/readable.ml";;
needs "Multivariate/determinants.ml";;

ParseAsInfix("∉",(11, "right"));;

let NOTIN = NewDefinition `;
  ∀a l. a ∉ l ⇔ ¬(a ∈ l)`;;

let DIFF_UNION = theorem `;
  ∀u s t. u ━ (s ∪ t) = (u ━ s) ∩ (u ━ t)
  by set`;;

let DIFF_REFL = theorem `;
  ∀u t. t ⊂ u ⇒ u ━ (u ━ t) = t
  by set`;;

let SUBSET_COMPLEMENT = theorem `;
  ∀s t A. s ⊂ A  ⇒  (s ⊂ A ━ t ⇔ s ∩ t = ∅)
  by set`;;

let COMPLEMENT_DISJOINT = theorem `;
  ∀A s t. s ⊂ A  ⇒  (s ⊂ t ⇔ s ∩ (A ━ t) = ∅)
  by set`;;

let COMPLEMENT_DUALITY = theorem `;
  ∀A s t. s ⊂ A ∧ t ⊂ A  ⇒  (s = t ⇔ A ━ s = A ━ t)
  by set`;;

let COMPLEMENT_DUALITY_UNION = theorem `;
  ∀A s t. s ⊂ A ∧ t ⊂ A ∧ u ⊂ A  ⇒  (s = t ∪ u ⇔ A ━ s = (A ━ t) ∩ (A ━ u))
  by set`;;

let SUBSET_DUALITY = theorem `;
  ∀s t u. t ⊂ u ⇒ s ━ u ⊂ s ━ t
  by set`;;

let COMPLEMENT_INTER_DIFF = theorem `;
  ∀A s t. s ⊂ A  ⇒  s ━ t = s ∩ (A ━ t)
  by set`;;

let INTERS_SUBSET = theorem `;
  ∀f t. ¬(f = ∅) ∧ (∀s. s ∈ f ⇒ s ⊂ t)  ⇒  INTERS f ⊂ t
  by set`;;

let IN_SET_FUNCTION_PREDICATE = theorem `;
  ∀x f P. x ∈ {f y | P y}  ⇔  ∃y. x = f y ∧ P y
  by set`;;

let INTER_TENSOR = theorem `;
  ∀s s' t t'.  s ⊂ s' ∧ t ⊂ t'  ⇒  s ∩ t ⊂ s' ∩ t'
  by set`;;

let UNION_TENSOR = theorem `;
  ∀s s' t t'.  s ⊂ s' ∧ t ⊂ t'  ⇒  s ∪ t ⊂ s' ∪ t'
  by set`;;

let ExistsTensorInter = theorem `;
  ∀F G H.  (∀x y. F x ∧ G y  ⇒ H (x ∩ y))  ⇒
    (∃x. F x) ∧ (∃y. G y) ⇒ (∃z. H z)
  by fol`;;

let istopology = NewDefinition `;
  istopology (X, L)  ⇔
  (∀U. U ∈ L  ⇒  U ⊂ X)  ∧  ∅ ∈ L  ∧  X ∈ L  ∧
  (∀s t. s ∈ L ∧ t ∈ L  ⇒ s ∩ t ∈ L)  ∧ ∀k. k ⊂ L  ⇒  UNIONS k ∈ L`;;

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
  ∃t. istopology t
  by fol ExistsTopology`;;

let topology_tybij =
  new_type_definition "topology" ("mk_topology","dest_topology")
  topology_tybij_th;;

let ISTOPOLOGYdest_topology = theorem `;
  ∀α. istopology (dest_topology α)
  by fol topology_tybij`;;

let OpenIn = NewDefinition `;
  ∀α. open_in α = OpenSets (dest_topology α)`;;

let topspace = NewDefinition `;
  ∀α. topspace α = UnderlyingSpace (dest_topology  α)`;;

let TopologyPAIR = theorem `;
  ∀α.  dest_topology α = (topspace α, open_in α)
  by rewrite PAIR_EQ OpenIn topspace UnderlyingSpace OpenSets`;;

let Topology_Eq = theorem `;
  ∀α β.  topspace α =  topspace β  ∧  (∀U. open_in α U ⇔ open_in β U)
    ⇔ α = β

  proof
    intro_TAC ∀α β;
    eq_tac     [Right] by fol;
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

let OPEN_IN_SUBSET = theorem `;
  ∀α s.  open_in α s  ⇒  s ⊂ topspace α
  by fol OpenInCLAUSES`;;

let OPEN_IN_EMPTY = theorem `;
  ∀α. open_in α ∅
  by fol OpenInCLAUSES`;;

let OPEN_IN_INTER = theorem `;
  ∀α s t. open_in α s ∧ open_in α t  ⇒  open_in α (s ∩ t)
  by fol OpenInCLAUSES`;;

let OPEN_IN_UNIONS = theorem `;
  ∀α k. (∀s. s ∈ k ⇒ open_in α s)  ⇒  open_in α (UNIONS k)
  by fol OpenInCLAUSES`;;

let OpenInUnderlyingSpace = theorem `;
  ∀α X. topspace α = X  ⇒  open_in α X
  by fol OpenInCLAUSES`;;

let OPEN_IN_UNION = theorem `;
  ∀α s t. open_in α s ∧ open_in α t  ⇒  open_in α (s ∪ t)

  proof
    intro_TAC ∀α s t, H;
    ∀x. x ∈ {s, t} ⇔ x = s ∨ x = t     [] by fol IN_INSERT NOT_IN_EMPTY;
    fol - UNIONS_2 H OPEN_IN_UNIONS;
  qed;
`;;

let OPEN_IN_TOPSPACE = theorem `;
  ∀α. open_in α (topspace α)
  by fol OpenInCLAUSES`;;

let OPEN_IN_INTERS = theorem `;
  ∀α s. FINITE s ∧ ¬(s = ∅) ∧ (∀t. t ∈ s  ⇒  open_in α t)
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
      fol xWorks Nonempty H1 sWorks OPEN_IN_INTER;
    end;
  qed;
`;;

let OPEN_IN_SUBOPEN = theorem `;
  ∀α s.  open_in α s ⇔ ∀x. x ∈ s ⇒ ∃t. open_in α t ∧ x ∈ t ∧ t ⊂ s

  proof
    intro_TAC ∀α s;
    eq_tac     [Left] by set;
    intro_TAC ALLtExist;
    consider f such that
    ∀x. x ∈ s  ⇒  open_in α (f x) ∧ x ∈ f x ∧ f x ⊂ s     [fExists] by fol ALLtExist SKOLEM_THM_GEN;
    s = UNIONS (IMAGE f s)     [] by set -;
    fol - fExists FORALL_IN_IMAGE OPEN_IN_UNIONS;
  qed;
`;;

let closed_in = NewDefinition `;
  ∀α s.  closed_in α s  ⇔
      s ⊂ topspace α ∧ open_in α (topspace α ━ s)`;;

let CLOSED_IN_SUBSET = theorem `;
  ∀α s. closed_in α s   ⇒  s ⊂ topspace α
  by fol closed_in`;;

let CLOSED_IN_EMPTY = theorem `;
  ∀α. closed_in α ∅
  by fol closed_in EMPTY_SUBSET DIFF_EMPTY OPEN_IN_TOPSPACE`;;

let CLOSED_IN_TOPSPACE = theorem `;
  ∀α. closed_in α (topspace α)
  by fol closed_in SUBSET_REFL DIFF_EQ_EMPTY OPEN_IN_EMPTY`;;

let CLOSED_IN_UNION = theorem `;
  ∀α s t. closed_in α s ∧ closed_in α t  ⇒  closed_in α (s ∪ t)

  proof
    intro_TAC ∀α s t, Hst;
    fol Hst closed_in DIFF_UNION UNION_SUBSET OPEN_IN_INTER;
  qed;
`;;

let CLOSED_IN_INTERS = theorem `;
  ∀α k.  ¬(k = ∅) ∧ (∀s. s ∈ k ⇒ closed_in α s)  ⇒  closed_in α (INTERS k)

  proof
    intro_TAC ∀α k, H1 H2;
    consider X such that X = topspace α     [Xdef] by fol;
    simplify GSYM Xdef closed_in DIFF_INTERS SIMPLE_IMAGE;
    fol H1 H2 Xdef INTERS_SUBSET closed_in FORALL_IN_IMAGE OPEN_IN_UNIONS;
  qed;
`;;

let CLOSED_IN_FORALL_IN = theorem `;
  ∀α P Q.  ¬(P = ∅) ∧ (∀a. P a ⇒ closed_in α {x | Q a x})  ⇒
    closed_in α {x | ∀a. P a ⇒ Q a x}

  proof
    intro_TAC ∀α P Q, Pnonempty H1;
    consider f such that f = {{x | Q a x} | P a}     [fDef] by fol;
    ¬(f = ∅)     [fNonempty] by set fDef Pnonempty;
    (∀a. P a ⇒ closed_in α {x | Q a x})  ⇔  (∀s. s ∈ f ⇒ closed_in α s)     [] by simplify fDef FORALL_IN_GSPEC;
    closed_in α (INTERS f)     [] by fol fNonempty H1 - CLOSED_IN_INTERS;
    MP_TAC -;
    {x | ∀a. P a ⇒ x ∈ {x | Q a x}} = {x | ∀a. P a ⇒ Q a x}     [] by set;
    simplify fDef INTERS_GSPEC -;
  qed;
`;;

let CLOSED_IN_INTER = theorem `;
  ∀α s t. closed_in α s ∧ closed_in α t ⇒ closed_in α (s ∩ t)

  proof
    intro_TAC ∀α s t, Hs Ht;
    rewrite GSYM INTERS_2;
    MATCH_MP_TAC CLOSED_IN_INTERS;
    set Hs Ht;
  qed;
`;;

let OPEN_IN_CLOSED_IN_EQ = theorem `;
  ∀α s. open_in α s  ⇔  s ⊂ topspace α ∧ closed_in α (topspace α ━ s)

  proof
    intro_TAC ∀α s;
    simplify closed_in SUBSET_DIFF OPEN_IN_SUBSET;
    fol SET_RULE [X ━ (X ━ s) = X ∩ s  ∧  (s ⊂ X ⇒ X ∩ s = s)] OPEN_IN_SUBSET;
  qed;
`;;

let OPEN_IN_CLOSED_IN = theorem `;
  ∀s. s ⊂ topspace α
    ⇒ (open_in α s ⇔ closed_in α (topspace α ━ s))
  by fol OPEN_IN_CLOSED_IN_EQ`;;

let OPEN_IN_DIFF = theorem `;
  ∀α s t.  open_in α s ∧ closed_in α t  ⇒  open_in α (s ━ t)

  proof
    intro_TAC ∀α s t, H1 H2;
    consider X such that X = topspace α     [Xdef] by fol;
    fol COMPLEMENT_INTER_DIFF OPEN_IN_SUBSET - H1 H2 closed_in OPEN_IN_INTER;
  qed;
`;;

let CLOSED_IN_DIFF = theorem `;
  ∀α s t.  closed_in α s ∧ open_in α t  ⇒  closed_in α (s ━ t)

  proof
    intro_TAC ∀α s t, H1 H2;
    consider X such that X = topspace α     [Xdef] by fol;
    fol COMPLEMENT_INTER_DIFF H1 - OPEN_IN_SUBSET SUBSET_DIFF DIFF_REFL H2 closed_in CLOSED_IN_INTER;
  qed;
`;;

let CLOSED_IN_UNIONS = theorem `;
  ∀α s.  FINITE s ∧ (∀t. t ∈ s ⇒ closed_in α t)
    ⇒ closed_in α (UNIONS s)

  proof
    intro_TAC ∀α;
    rewrite IMP_CONJ;
    MATCH_MP_TAC FINITE_INDUCT;
    fol UNIONS_INSERT UNIONS_0 CLOSED_IN_EMPTY IN_INSERT CLOSED_IN_UNION;
  qed;
`;;

let subtopology = NewDefinition `;
  ∀α u.  subtopology α u = mk_topology (u, {s ∩ u | open_in α s})`;;

let IstopologySubtopology = theorem `;
  ∀α u:A->bool. u ⊂ topspace α  ⇒  istopology (u, {s ∩ u | open_in α s})

  proof
    intro_TAC ∀α u, H1;
    ∅ = ∅ ∩ u ∧ open_in α ∅     [emptysetOpen] by fol INTER_EMPTY OPEN_IN_EMPTY;
    u = topspace α ∩ u ∧ open_in α (topspace α)     [uOpen] by fol OPEN_IN_TOPSPACE H1 INTER_COMM SUBSET_INTER_ABSORPTION;
    ∀s' s. open_in α s' ∧ open_in α s  ⇒  open_in α (s' ∩ s)  ∧
    (s' ∩ u) ∩ (s ∩ u) = (s' ∩ s) ∩ u     [interOpen]
    proof
      intro_TAC ∀s' s, H1 H2;
      set MESON [H1; H2; OPEN_IN_INTER] [open_in α (s' ∩ s)];
    qed;
    ∀k. k ⊂ {s | open_in α s}  ⇒  open_in α (UNIONS k)  ∧
    UNIONS (IMAGE (λs. s ∩ u) k) = (UNIONS k) ∩ u     [unionsOpen]
    proof
      intro_TAC ∀k, kProp;
      open_in α (UNIONS k)     [] by fol kProp SUBSET IN_ELIM_THM OPEN_IN_UNIONS;
      simplify - UNIONS_IMAGE UNIONS_GSPEC INTER_UNIONS;
    qed;
    {s ∩ u | open_in α s} = IMAGE (λs. s ∩ u) {s | open_in α s}     [] by set;
    simplify istopology IN_SET_FUNCTION_PREDICATE LEFT_IMP_EXISTS_THM INTER_SUBSET - FORALL_SUBSET_IMAGE;
    fol  emptysetOpen uOpen interOpen unionsOpen;
  qed;
`;;

let OpenInSubtopology = theorem `;
  ∀α u s. u ⊂ topspace α ⇒
    (open_in (subtopology α u) s  ⇔  ∃t. open_in α t ∧ s = t ∩ u)

  proof
    intro_TAC ∀α u s, H1;
    open_in (subtopology α u) = OpenSets (u,{s ∩ u | open_in α s})     [] by fol subtopology H1 IstopologySubtopology topology_tybij OpenIn;
    rewrite - OpenSets PAIR_EQ SND EXTENSION IN_ELIM_THM;
  qed;
`;;

let TopspaceSubtopology = theorem `;
  ∀α u. u ⊂ topspace α  ⇒  topspace (subtopology α u) = u

  proof
    intro_TAC ∀α u , H1;
    topspace (subtopology α u) = UnderlyingSpace (u,{s ∩ u | open_in α s})     [] by fol subtopology H1 IstopologySubtopology topology_tybij topspace;
    rewrite - UnderlyingSpace PAIR_EQ FST;
    fol  INTER_COMM H1 SUBSET_INTER_ABSORPTION;
  qed;
`;;

let OpenInRefl = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  open_in (subtopology α s) s
  by fol TopspaceSubtopology OPEN_IN_TOPSPACE`;;

let ClosedInRefl = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  closed_in (subtopology α s) s
  by fol TopspaceSubtopology CLOSED_IN_TOPSPACE`;;

let ClosedInSubtopology = theorem `;
  ∀α u C.  u ⊂ topspace α  ⇒
    (closed_in (subtopology α u) C  ⇔  ∃D. closed_in α D ∧ C = D ∩ u)

  proof
    intro_TAC ∀α u C, H1;
    consider X such that
    X = topspace α ∧ u ⊂ X     [Xdef] by fol H1;
    closed_in (subtopology α u) C  ⇔
    ∃t. C ⊂ u ∧ t ⊂ X ∧ open_in α t ∧ u ━ C = t ∩ u     [] by fol closed_in H1 Xdef OpenInSubtopology OPEN_IN_SUBSET TopspaceSubtopology;
    closed_in (subtopology α u) C  ⇔
    ∃D. C ⊂ u ∧ D ⊂ X ∧ open_in α (X ━ D) ∧ u ━ C = (X ━ D) ∩ u     []
    proof
      rewrite -;
      eq_tac     [Left]
      proof
        STRIP_TAC;     exists_TAC X ━ t;
        ASM_SIMP_TAC H1 OPEN_IN_SUBSET DIFF_REFL SUBSET_DIFF;
      qed;
      STRIP_TAC;     exists_TAC X ━ D;
      ASM_SIMP_TAC SUBSET_DIFF;
    qed;
    simplify - GSYM Xdef H1 closed_in;
    ∀D C. C ⊂ u ∧ u ━ C = (X ━ D) ∩ u  ⇔  C = D ∩ u     [] by set Xdef DIFF_REFL INTER_SUBSET;
    fol -;
  qed;
`;;

let OPEN_IN_SUBTOPOLOGY_EMPTY = theorem `;
  ∀α s. open_in (subtopology α ∅) s  ⇔  s = ∅

  proof
    simplify EMPTY_SUBSET OpenInSubtopology INTER_EMPTY;
    fol  OPEN_IN_EMPTY;
  qed;
`;;

let CLOSED_IN_SUBTOPOLOGY_EMPTY = theorem `;
  ∀α s. closed_in (subtopology α ∅) s  ⇔  s = ∅

  proof
    simplify EMPTY_SUBSET ClosedInSubtopology INTER_EMPTY;
    fol  CLOSED_IN_EMPTY;
  qed;
`;;

let SUBTOPOLOGY_TOPSPACE = theorem `;
  ∀α. subtopology α (topspace α) = α

  proof
    intro_TAC ∀α;
    topspace (subtopology α (topspace α)) = topspace α     [topXsub] by simplify SUBSET_REFL TopspaceSubtopology;
    simplify topXsub GSYM Topology_Eq;
    fol MESON [SUBSET_REFL] [topspace α ⊂ topspace α] OpenInSubtopology OPEN_IN_SUBSET SUBSET_INTER_ABSORPTION;
  qed;
`;;

let OpenInImpSubset = theorem `;
  ∀α s t.  s ⊂ topspace α  ⇒
    open_in (subtopology α s) t  ⇒  t ⊂ s
  by fol OpenInSubtopology INTER_SUBSET`;;

let ClosedInImpSubset = theorem `;
  ∀α s t.  s ⊂ topspace α  ⇒
    closed_in (subtopology α s) t  ⇒  t ⊂ s
  by fol ClosedInSubtopology INTER_SUBSET`;;

let OpenInSubtopologyUnion = theorem `;
  ∀α s t u.  t ⊂ topspace α  ∧  u ⊂ topspace α  ⇒
    open_in (subtopology α t) s  ∧  open_in (subtopology α u) s
    ⇒  open_in (subtopology α (t ∪ u)) s

  proof
    intro_TAC ∀α s t u, Ht Hu;
    simplify Ht Hu Ht Hu UNION_SUBSET OpenInSubtopology;
    intro_TAC sOpenSub_t sOpenSub_u;
    consider a b such that
    open_in α a  ∧  s = a ∩ t  ∧
    open_in α b  ∧  s = b ∩ u     [abExist] by fol sOpenSub_t sOpenSub_u;
    exists_TAC a ∩ b;
    set MESON [abExist; OPEN_IN_INTER] [open_in α (a ∩ b)] abExist;
  qed;
`;;

let ClosedInSubtopologyUnion = theorem `;
  ∀α s t u.  t ⊂ topspace α  ∧  u ⊂ topspace α  ⇒
    closed_in (subtopology α t) s  ∧  closed_in (subtopology α u) s
    ⇒  closed_in (subtopology α (t ∪ u)) s

  proof
    intro_TAC ∀α s t u, Ht Hu;
    simplify Ht Hu Ht Hu UNION_SUBSET ClosedInSubtopology;
    intro_TAC sClosedSub_t sClosedSub_u;
    consider a b such that
    closed_in α a  ∧  s = a ∩ t  ∧
    closed_in α b  ∧  s = b ∩ u     [abExist] by fol sClosedSub_t sClosedSub_u;
    exists_TAC a ∩ b;
    set MESON [abExist; CLOSED_IN_INTER] [closed_in α (a ∩ b)] abExist;
  qed;
`;;

let OpenInSubtopologyInterOpen = theorem `;
  ∀α s t u.  u ⊂ topspace α  ⇒
    open_in (subtopology α u) s  ∧  open_in α t
    ⇒ open_in (subtopology α u) (s ∩ t)

  proof
    intro_TAC ∀α s t u, H1, sOpenSub_t tOpen;
    consider a b such that
    open_in α a  ∧  s = a ∩ u  ∧  b = a ∩ t     [aExists] by fol sOpenSub_t H1 OpenInSubtopology;
    fol - tOpen OPEN_IN_INTER INTER_ACI H1 OpenInSubtopology;
  qed;
`;;

let OpenInOpenInter = theorem `;
  ∀α u s.  u ⊂ topspace α  ⇒ open_in α s
    ⇒  open_in (subtopology α u) (u ∩ s)
  by fol INTER_COMM OpenInSubtopology`;;

let OpenOpenInTrans = theorem `;
  ∀α s t.  open_in α s ∧ open_in α t ∧ t ⊂ s
    ⇒ open_in (subtopology α s) t
  by fol OPEN_IN_SUBSET SUBSET_INTER_ABSORPTION OpenInSubtopology`;;

let ClosedClosedInTrans = theorem `;
  ∀α s t.  closed_in α s ∧ closed_in α t ∧ t ⊂ s
    ⇒ closed_in (subtopology α s) t
  by fol CLOSED_IN_SUBSET SUBSET_INTER_ABSORPTION ClosedInSubtopology`;;

let OpenSubset = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒
    s ⊂ t  ∧  open_in α s ⇒ open_in (subtopology α t) s
  by fol OpenInSubtopology SUBSET_INTER_ABSORPTION`;;

let ClosedSubsetEq = theorem `;
  ∀α u s.  u ⊂ topspace α  ⇒
    closed_in α s  ⇒  (closed_in (subtopology α u) s  ⇔  s ⊂ u)
  by fol ClosedInSubtopology INTER_SUBSET SUBSET_INTER_ABSORPTION`;;

let ClosedInInterClosed = theorem `;
  ∀α s t u.  u ⊂ topspace α  ⇒
        closed_in (subtopology α u) s ∧ closed_in α t
        ⇒ closed_in (subtopology α u) (s ∩ t)

  proof
    intro_TAC ∀α s t u, H1, sClosedSub_t tClosed;
    consider a b such that
    closed_in α a  ∧  s = a ∩ u  ∧  b = a ∩ t     [aExists] by fol sClosedSub_t H1 ClosedInSubtopology;
    fol - tClosed CLOSED_IN_INTER INTER_ACI H1 ClosedInSubtopology;
  qed;
`;;

let ClosedInClosedInter = theorem `;
  ∀α u s.  u ⊂ topspace α  ⇒
    closed_in α s  ⇒  closed_in (subtopology α u) (u ∩ s)
  by fol INTER_COMM ClosedInSubtopology`;;

let ClosedSubset = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒
    s ⊂ t  ∧  closed_in α s  ⇒  closed_in (subtopology α t) s
  by fol ClosedInSubtopology SUBSET_INTER_ABSORPTION`;;

let OpenInSubsetTrans = theorem `;
  ∀α s t u.  u ⊂ topspace α  ∧  t ⊂ topspace α  ⇒
    open_in (subtopology α u) s  ∧  s ⊂ t  ∧  t ⊂ u
    ⇒ open_in (subtopology α t) s

  proof
    intro_TAC ∀α s t u, uSubset tSubset;
    simplify uSubset tSubset OpenInSubtopology;
    intro_TAC sOpen_u s_t t_u;
    consider a such that
    open_in α a  ∧  s = a ∩ u     [aExists] by fol uSubset sOpen_u OpenInSubtopology;
    set aExists s_t t_u;
  qed;
`;;

let ClosedInSubsetTrans = theorem `;
  ∀α s t u.  u ⊂ topspace α  ∧  t ⊂ topspace α  ⇒
        closed_in (subtopology α u) s  ∧  s ⊂ t  ∧  t ⊂ u
        ⇒ closed_in (subtopology α t) s

  proof
    intro_TAC ∀α s t u, uSubset tSubset;
    simplify uSubset tSubset ClosedInSubtopology;
    intro_TAC sClosed_u s_t t_u;
    consider a such that
    closed_in α a  ∧  s = a ∩ u     [aExists] by fol uSubset sClosed_u ClosedInSubtopology;
    set aExists s_t t_u;
  qed;
`;;

let OpenInTrans = theorem `;
  ∀α s t u.  t ⊂ topspace α  ∧  u ⊂ topspace α  ⇒
    open_in (subtopology α t) s   ∧  open_in (subtopology α u) t
    ⇒ open_in (subtopology α u) s

  proof
    intro_TAC ∀α s t u, H1 H2;
    simplify H1 H2 OpenInSubtopology;
    fol H1 H2 OpenInSubtopology OPEN_IN_INTER INTER_ASSOC;
  qed;
`;;

let OpenInTransEq = theorem `;
  ∀α s t.  t ⊂ topspace α  ∧  s ⊂ topspace α  ⇒
    ((∀u. open_in (subtopology α t) u  ⇒  open_in (subtopology α s) t)
    ⇔ open_in (subtopology α s) t)
  by fol OpenInTrans OpenInRefl`;;

let OpenInOpenTrans = theorem `;
  ∀α u s.  u ⊂ topspace α  ⇒
    open_in (subtopology α u) s ∧ open_in α u  ⇒  open_in α s
  by fol OpenInSubtopology OPEN_IN_INTER`;;

let OpenInSubtopologyTrans = theorem `;
  ∀α s t u.  t ⊂ topspace α  ∧  u ⊂ topspace α  ⇒
    open_in (subtopology α t) s  ∧  open_in (subtopology α u) t
    ⇒ open_in (subtopology α u) s

  proof
    simplify OpenInSubtopology;
    fol  OPEN_IN_INTER INTER_ASSOC;
  qed;
`;;

let SubtopologyOpenInSubopen = theorem `;
  ∀α u s.  u ⊂ topspace α ⇒
    (open_in (subtopology α u) s  ⇔
    s ⊂ u  ∧  ∀x. x ∈ s ⇒ ∃t. open_in α t  ∧  x ∈ t  ∧  t ∩ u ⊂ s)

  proof
    intro_TAC ∀α u s, H1;
    rewriteL OPEN_IN_SUBOPEN;
    simplify H1 OpenInSubtopology;
    eq_tac     [Right] by fol SUBSET IN_INTER;
    intro_TAC H2;
    conj_tac     [Left]
    proof     simplify SUBSET;     fol H2 IN_INTER;     qed;
    intro_TAC ∀x, xs;
    consider t such that
    open_in α t ∧ x ∈ t ∩ u ∧ t ∩ u ⊂ s     [tExists] by fol H2 xs;
    fol  - IN_INTER;
  qed;
`;;

let ClosedInSubtopologyTrans = theorem `;
  ∀α s t u.  t ⊂ topspace α  ∧  u ⊂ topspace α  ⇒
    closed_in (subtopology α t) s  ∧  closed_in (subtopology α u) t
    ⇒ closed_in (subtopology α u) s

  proof
    simplify ClosedInSubtopology;
    fol  CLOSED_IN_INTER INTER_ASSOC;
  qed;
`;;

let ClosedInSubtopologyTransEq = theorem `;
  ∀α s t.  t ⊂ topspace α  ∧  s ⊂ topspace α  ⇒
    ((∀u. closed_in (subtopology α t) u  ⇒  closed_in (subtopology α s) t)
    ⇔ closed_in (subtopology α s) t)

  proof
    intro_TAC ∀α s t, H1 H2;
    fol H1 H2 ClosedInSubtopologyTrans CLOSED_IN_TOPSPACE;
  qed;
`;;

let ClosedInClosedTrans = theorem `;
  ∀α s t.  u ⊂ topspace α  ⇒
    closed_in (subtopology α u) s ∧ closed_in α u ⇒ closed_in α s
  by fol ClosedInSubtopology CLOSED_IN_INTER`;;

let OpenInSubtopologyInterSubset = theorem `;
  ∀α s u v.  u ⊂ topspace α  ∧  v ⊂ topspace α  ⇒
    open_in (subtopology α u) (u ∩ s)  ∧  v ⊂ u
    ⇒ open_in (subtopology α v) (v ∩ s)

  proof
    simplify OpenInSubtopology;
    set;
  qed;
`;;

let OpenInOpenEq = theorem `;
  ∀α s t.  s ⊂ topspace α  ⇒
    open_in α s  ⇒  (open_in (subtopology α s) t  ⇔  open_in α t ∧ t ⊂ s)
  by fol OpenOpenInTrans OPEN_IN_SUBSET TopspaceSubtopology OpenInOpenTrans`;;

let ClosedInClosedEq = theorem `;
  ∀α s t.  s ⊂ topspace α  ⇒  closed_in α s  ⇒
    (closed_in (subtopology α s) t  ⇔  closed_in α t ∧ t ⊂ s)
  by fol ClosedClosedInTrans CLOSED_IN_SUBSET TopspaceSubtopology ClosedInClosedTrans`;;

let OpenImpliesSubtopologyInterOpen = theorem `;
  ∀α u s.  u ⊂ topspace α  ⇒
    open_in α s  ⇒  open_in (subtopology α u) (u ∩ s)
    by fol OpenInSubtopology INTER_COMM`;;

let OPEN_IN_EXISTS_IN = theorem `;
  ∀α P Q.  (∀a. P a ⇒ open_in α {x | Q a x})  ⇒
    open_in α {x | ∃a. P a ∧ Q a x}

  proof
    intro_TAC ∀α P Q, H1;
    consider f such that f = {{x | Q a x} | P a}     [fDef] by fol;
    (∀a. P a ⇒ open_in α {x | Q a x})  ⇔  (∀s. s ∈ f ⇒ open_in α s)     [] by simplify fDef FORALL_IN_GSPEC;
    MP_TAC MESON [H1; -; OPEN_IN_UNIONS] [open_in α  (UNIONS f)];
    simplify fDef UNIONS_GSPEC;
    set;
  qed;
`;;

let Connected_DEF = NewDefinition `;
  ∀α. Connected α ⇔
    ¬(∃e1 e2. open_in α e1  ∧  open_in α e2  ∧  topspace α = e1 ∪ e2  ∧
    e1 ∩ e2 = ∅  ∧  ¬(e1 = ∅)  ∧  ¬(e2 = ∅))`;;

let ConnectedClosedHelp = theorem `;
  ∀α e1 e2. topspace α = e1 ∪ e2  ∧  e1 ∩ e2 = ∅  ⇒
    (closed_in α e1  ∧  closed_in α e2  ⇔  open_in α e1  ∧  open_in α e2)

  proof
    intro_TAC ∀α e1 e2, H1 H2;
    e1 = topspace α ━ e2  ∧  e2 = topspace α ━ e1     [e12Complements] by set H1 H2;
    fol H1 SUBSET_UNION e12Complements OPEN_IN_CLOSED_IN_EQ;
  qed;
`;;

let ConnectedClosed = theorem `;
  ∀α. Connected α  ⇔
    ¬(∃e1 e2. closed_in α e1  ∧  closed_in α e2  ∧
    topspace α = e1 ∪ e2  ∧  e1 ∩ e2 = ∅  ∧  ¬(e1 = ∅) ∧ ¬(e2 = ∅))

  proof
    rewrite Connected_DEF;
    fol ConnectedClosedHelp;
  qed;
`;;

let ConnectedOpenIn = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    (Connected (subtopology α s)  ⇔  ¬(∃e1 e2.
    open_in (subtopology α s) e1  ∧  open_in (subtopology α s) e2  ∧
    s ⊂ e1 ∪ e2  ∧  e1 ∩ e2 = ∅  ∧  ¬(e1 = ∅)  ∧  ¬(e2 = ∅)))

  proof
    simplify Connected_DEF TopspaceSubtopology;
    fol SUBSET_REFL OpenInImpSubset UNION_SUBSET SUBSET_ANTISYM;
  qed;
`;;

let ConnectedClosedIn = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    (Connected (subtopology α s)  ⇔  ¬(∃e1 e2.
    closed_in (subtopology α s) e1  ∧  closed_in (subtopology α s) e2  ∧
    s ⊂ e1 ∪ e2  ∧  e1 ∩ e2 = ∅  ∧  ¬(e1 = ∅)  ∧  ¬(e2 = ∅)))

  proof
    simplify ConnectedClosed TopspaceSubtopology;
    fol SUBSET_REFL ClosedInImpSubset UNION_SUBSET SUBSET_ANTISYM;
  qed;
`;;

let ConnectedSubtopology = theorem `;
  ∀α s. s ⊂ topspace α  ⇒
    (Connected (subtopology α s)  ⇔
    ¬(∃e1 e2. open_in α e1  ∧  open_in α e2  ∧  s ⊂ e1 ∪ e2  ∧
    e1 ∩ e2 ∩ s = ∅  ∧  ¬(e1 ∩ s = ∅)  ∧  ¬(e2 ∩ s = ∅)))

  proof
    intro_TAC ∀α s, H1;
    simplify H1 Connected_DEF OpenInSubtopology TopspaceSubtopology;
    AP_TERM_TAC;
    eq_tac     [Left]
    proof
    intro_TAC H2;
    consider t1 t2 such that
    open_in α t1  ∧  open_in α t2  ∧  s = (t1 ∩ s) ∪ (t2 ∩ s)  ∧
    (t1 ∩ s) ∩ (t2 ∩ s) = ∅  ∧  ¬(t1 ∩ s = ∅)  ∧  ¬(t2 ∩ s = ∅)     [t12Exist] by fol H2;
    s ⊂ t1 ∪ t2  ∧  t1 ∩ t2 ∩ s = ∅     [] by set t12Exist;
    fol t12Exist -;
    qed;
    rewrite LEFT_IMP_EXISTS_THM;
    intro_TAC ∀e1 e2, e12Exist;
    exists_TAC e1 ∩ s;
    exists_TAC e2 ∩ s;
    set e12Exist;
  qed;
`;;

let ConnectedSubtopology_ALT = theorem `;
  ∀α s. s ⊂ topspace α  ⇒
    (Connected (subtopology α s)  ⇔
    ∀e1 e2. open_in α e1  ∧  open_in α e2  ∧ s ⊂ e1 ∪ e2  ∧  e1 ∩ e2 ∩ s = ∅
    ⇒ e1 ∩ s = ∅  ∨  e2 ∩ s = ∅)

  proof     simplify ConnectedSubtopology;     fol;     qed;
`;;

let ConnectedClosedSubtopology = theorem `;
  ∀α s. s ⊂ topspace α  ⇒
    (Connected (subtopology α s)  ⇔
    ¬(∃e1 e2. closed_in α e1  ∧  closed_in α e2  ∧  s ⊂ e1 ∪ e2  ∧
    e1 ∩ e2 ∩ s = ∅  ∧  ¬(e1 ∩ s = ∅)  ∧  ¬(e2 ∩ s = ∅)))

  proof
    intro_TAC ∀α s, H1;
    simplify H1 ConnectedSubtopology;
    AP_TERM_TAC;
    eq_tac     [Left]
    proof
      rewrite LEFT_IMP_EXISTS_THM;
      intro_TAC ∀e1 e2, e12Exist;
      exists_TAC topspace α ━ e2;
      exists_TAC topspace α ━ e1;
      simplify OPEN_IN_SUBSET H1 SUBSET_DIFF DIFF_REFL closed_in e12Exist;
      set H1 e12Exist;
    qed;
    rewrite LEFT_IMP_EXISTS_THM;
    intro_TAC ∀e1 e2, e12Exist;
    exists_TAC topspace α ━ e2;
    exists_TAC topspace α ━ e1;
    e1 ⊂ topspace α  ∧  e2 ⊂ topspace α     [e12Top] by fol closed_in e12Exist;
    simplify DIFF_REFL SUBSET_DIFF e12Top OPEN_IN_CLOSED_IN;
    set H1 e12Exist;
  qed;
`;;

let ConnectedClopen = theorem `;
  ∀α. Connected α  ⇔
    ∀t. open_in α t ∧ closed_in α t  ⇒  t = ∅ ∨ t = topspace α

  proof
    intro_TAC ∀α;
    simplify Connected_DEF closed_in TAUT [(¬a ⇔ b) ⇔ (a ⇔ ¬b)] NOT_FORALL_THM NOT_IMP DE_MORGAN_THM;
    eq_tac     [Left]
    proof
      rewrite LEFT_IMP_EXISTS_THM;     intro_TAC ∀e1 e2, H1 H2 H3 H4 H5 H6;
      exists_TAC e1;
      e1 ⊂ topspace α  ∧  e2 = topspace α ━ e1  ∧  ¬(e1 = topspace alpha)     [] by set H3 H4 H6;
      fol H1 - H2 H5;
    qed;
    rewrite LEFT_IMP_EXISTS_THM;     intro_TAC ∀t, H1;
    exists_TAC t;     exists_TAC topspace α ━ t;
    set H1;
  qed;
`;;

let ConnectedClosedSet = theorem `;
  ∀α s. s ⊂ topspace α  ⇒  closed_in α s  ⇒
    (Connected (subtopology α s)  ⇔  ¬(∃e1 e2.
    closed_in α e1  ∧  closed_in α e2  ∧
    ¬(e1 = ∅)  ∧  ¬(e2 = ∅)  ∧  e1 ∪ e2 = s  ∧  e1 ∩ e2 = ∅))

  proof
    intro_TAC ∀α s, H1, H2;
    simplify H1 ConnectedClosedSubtopology;
    AP_TERM_TAC;
    eq_tac     [Left]
    proof
      rewrite LEFT_IMP_EXISTS_THM;     intro_TAC ∀e1 e2, H3 H4 H5 H6 H7 H8;
      exists_TAC e1 ∩ s;     exists_TAC e2 ∩ s;
      simplify H2 H3 H4 H7 H8 CLOSED_IN_INTER;
      set H5 H6;
    qed;
    rewrite LEFT_IMP_EXISTS_THM;     intro_TAC ∀e1 e2, H3 H4 H5 H6 H7 H8;
    exists_TAC e1;     exists_TAC e2;
    set H3 H4 H7 H8 H5 H6;
  qed;
`;;

let ConnectedOpenSet = theorem `;
  ∀α s.  open_in α s  ⇒
    (Connected (subtopology α s) ⇔
    ¬(∃e1 e2.  open_in α e1  ∧  open_in α e2  ∧
    ¬(e1 = ∅)  ∧  ¬(e2 = ∅)  ∧  e1 ∪ e2 = s  ∧  e1 ∩ e2 = ∅))

  proof
    intro_TAC ∀α s, H1;
    simplify H1 OPEN_IN_SUBSET ConnectedSubtopology;
    AP_TERM_TAC;
    eq_tac     [Left]
    proof
      rewrite LEFT_IMP_EXISTS_THM;     intro_TAC ∀e1 e2, H3 H4 H5 H6 H7 H8;
      exists_TAC e1 ∩ s;     exists_TAC e2 ∩ s;
      e1 ⊂ topspace α  ∧  e2 ⊂ topspace α     [e12Subsets] by fol H3 H4 OPEN_IN_SUBSET;
      simplify H1 H3 H4 OPEN_IN_INTER H7 H8;
      set e12Subsets H5 H6;
    qed;
    rewrite LEFT_IMP_EXISTS_THM;     intro_TAC ∀e1 e2, H3 H4 H5 H6 H7 H8;
    exists_TAC e1;     exists_TAC e2;
    set H3 H4 H7 H8 H5 H6;
  qed;
`;;

let ConnectedEmpty = theorem `;
  ∀α. Connected (subtopology α ∅)

  proof
    simplify Connected_DEF INTER_EMPTY EMPTY_SUBSET TopspaceSubtopology;
    fol UNION_SUBSET SUBSET_EMPTY;
  qed;
`;;

let ConnectedSing = theorem `;
  ∀α a. a ∈ topspace α  ⇒  Connected (subtopology α {a})

  proof
    simplify Connected_DEF SING_SUBSET TopspaceSubtopology;
    set;
  qed;
`;;

let ConnectedUnions = theorem `;
  ∀α P. (∀s. s ∈ P ⇒ s ⊂ topspace α)  ⇒
    (∀s. s ∈ P ⇒ Connected (subtopology α s)) ∧ ¬(INTERS P = ∅)
        ⇒ Connected (subtopology α (UNIONS P))

  proof
    intro_TAC ∀α P, H1;
    simplify H1 ConnectedSubtopology UNIONS_SUBSET NOT_EXISTS_THM;
    intro_TAC allConnected PnotDisjoint, ∀[d/e1] [e/e2];
    consider a such that
    ∀t. t ∈ P ⇒ a ∈ t     [aInterP] by fol PnotDisjoint MEMBER_NOT_EMPTY IN_INTERS;
    ONCE_REWRITE_TAC TAUT [∀p. ¬p ⇔ p ⇒ F];
    intro_TAC dOpen eOpen Pde deDisjoint dNonempty eNonempty;
    a ∈ d ∨ a ∈ e     [adORae] by set aInterP Pde dNonempty;
    consider s x t y such that
    s ∈ P  ∧  x ∈ d ∩ s  ∧
    t ∈ P  ∧  y ∈ e ∩ t     [xdsANDyet] by set dNonempty eNonempty;
    d ∩ e ∩ s = ∅  ∧  d ∩ e ∩ t = ∅     [] by set - deDisjoint;
    (d ∩ s = ∅  ∨  e ∩ s = ∅)  ∧
    (d ∩ t = ∅  ∨  e ∩ t = ∅)     [] by fol xdsANDyet allConnected dOpen eOpen Pde -;
    set adORae xdsANDyet aInterP -;
  qed;
`;;

let ConnectedUnion = theorem `;
  ∀α s t.  s ⊂ topspace α  ∧  t ⊂ topspace α  ∧  ¬(s ∩ t = ∅)  ∧
    Connected (subtopology α s) ∧ Connected (subtopology α t)
    ⇒ Connected (subtopology α (s ∪ t))

  proof
    rewrite GSYM UNIONS_2 GSYM INTERS_2;
    intro_TAC ∀α s t, H1 H2 H3 H4 H5;
    ∀u. u ∈ {s, t}  ⇒  u ⊂ topspace α     [stEuclidean] by set H1 H2;
    ∀u. u ∈ {s, t}  ⇒  Connected (subtopology α u)     [] by set H4 H5;
    fol stEuclidean - H3 ConnectedUnions;
  qed;
`;;

let ConnectedDiffOpenFromClosed = theorem `;
  ∀α s t u.  u ⊂ topspace α  ⇒
    s ⊂ t  ∧  t ⊂ u ∧ open_in α s  ∧  closed_in α t  ∧
    Connected (subtopology α u)  ∧  Connected (subtopology α (t ━ s))
    ⇒ Connected (subtopology α (u ━ s))

  proof
    ONCE_REWRITE_TAC TAUT
    [∀a b c d e f g. (a ∧ b ∧ c ∧ d ∧ e ∧ f ⇒ g)  ⇔
    (a ∧ b ∧ c ∧ d ⇒ ¬g ⇒ f ⇒ ¬e)];
    intro_TAC ∀α s t u, uSubset, st tu sOpen tClosed;
    t ━ s ⊂ topspace α  ∧  u ━ s ⊂ topspace α     [] by fol uSubset sOpen OPEN_IN_SUBSET tClosed closed_in SUBSET_DIFF SUBSET_TRANS;
    simplify uSubset - ConnectedSubtopology;
    rewrite LEFT_IMP_EXISTS_THM;
    intro_TAC ∀[v/e1] [w/e2];
    intro_TAC vOpen wOpen u_sDisconnected vwDisjoint vNonempty wNonempty;
    rewrite NOT_EXISTS_THM;
    intro_TAC t_sConnected;
    t ━ s ⊂ v ∪ w  ∧  v ∩ w ∩ (t ━ s) = ∅     [] by set tu u_sDisconnected vwDisjoint;
    v ∩ (t ━ s) = ∅  ∨  w ∩ (t ━ s) = ∅     [] by fol t_sConnected vOpen wOpen -;
    case_split vEmpty | wEmpty by fol -;
    suppose v ∩ (t ━ s) = ∅;
      exists_TAC w ∪ s;     exists_TAC v ━ t;
      simplify vOpen wOpen sOpen tClosed OPEN_IN_UNION OPEN_IN_DIFF;
      set st tu u_sDisconnected vEmpty vwDisjoint wNonempty vNonempty;
    end;
    suppose w ∩ (t ━ s) = ∅;
      exists_TAC v ∪ s;     exists_TAC w ━ t;
      simplify vOpen wOpen sOpen tClosed OPEN_IN_UNION OPEN_IN_DIFF;
      set st tu u_sDisconnected wEmpty vwDisjoint wNonempty vNonempty;
    end;
  qed;
`;;

let LimitPointOf = NewDefinition `;
  ∀α s. LimitPointOf α s  =  {x | s ⊂ topspace α ∧ x ∈ topspace α ∧
    ∀t. x ∈ t ∧ open_in α t  ⇒  ∃y. ¬(y = x) ∧ y ∈ s ∧ y ∈ t}`;;

let IN_LimitPointOf = theorem `;
  ∀α s x.  s ⊂ topspace α  ⇒
    (x ∈ LimitPointOf α s  ⇔  x ∈ topspace α ∧
    ∀t. x ∈ t ∧ open_in α t  ⇒  ∃y. ¬(y = x) ∧ y ∈ s ∧ y ∈ t)
  by simplify IN_ELIM_THM LimitPointOf`;;

let NotLimitPointOf = theorem `;
  ∀α s x.  s ⊂ topspace α ∧ x ∈ topspace α  ⇒
    (x ∉ LimitPointOf α s  ⇔
    ∃t. x ∈ t  ∧  open_in α t  ∧  s ∩ (t ━ {x}) = ∅)

  proof
    ONCE_REWRITE_TAC TAUT [∀a b. (a ⇔ b)  ⇔  (¬a  ⇔ ¬b)];
    simplify ∉ NOT_EXISTS_THM IN_LimitPointOf
     TAUT [∀a b. ¬(a ∧ b ∧ c)  ⇔  a ∧ b ⇒ ¬c] GSYM MEMBER_NOT_EMPTY IN_INTER  IN_DIFF IN_SING;
     fol;
  qed;
`;;

let LimptSubset = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒
    s ⊂ t  ⇒  LimitPointOf α s ⊂ LimitPointOf α t

  proof
    intro_TAC ∀α s t, tTop, st;
    s ⊂ topspace α     [sTop] by fol tTop st SUBSET_TRANS;
    simplify tTop sTop IN_LimitPointOf SUBSET;
    fol st SUBSET;
  qed;
`;;

let ClosedLimpt = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    (closed_in α s  ⇔  LimitPointOf α s ⊂ s)

  proof
    intro_TAC ∀α s, H1;
    simplify H1 closed_in;
    ONCE_REWRITE_TAC OPEN_IN_SUBOPEN;
    simplify H1 IN_LimitPointOf SUBSET IN_DIFF;
    AP_TERM_TAC;
    ABS_TAC;
    fol OPEN_IN_SUBSET SUBSET;
  qed;
`;;

let LimptEmpty = theorem `;
  ∀α x.  x ∈ topspace α  ⇒  x ∉ LimitPointOf α ∅
  by fol EMPTY_SUBSET IN_LimitPointOf OPEN_IN_TOPSPACE NOT_IN_EMPTY ∉`;;
 
let NoLimitPointImpClosed = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  (∀x. x ∉ LimitPointOf α s)  ⇒  closed_in α s
  by fol ClosedLimpt SUBSET ∉`;;

let LimitPointUnion = theorem `;
  ∀α s t.  s ∪ t ⊂ topspace α  ⇒
    LimitPointOf α (s ∪ t)  =  LimitPointOf α s  ∪  LimitPointOf α t

  proof
    intro_TAC ∀α s t, H1;
    s ⊂ topspace α ∧ t ⊂ topspace α     [stTop] by fol H1 UNION_SUBSET;
    rewrite EXTENSION IN_UNION;
    intro_TAC ∀x;
    case_split xNotTop | xTop by fol ∉;
    suppose x ∉ topspace α;
      fol xNotTop H1 stTop IN_LimitPointOf ∉;
    end;
    suppose x ∈ topspace α;
      ONCE_REWRITE_TAC TAUT [∀a b. (a ⇔ b)  ⇔  (¬a  ⇔ ¬b)];
      simplify GSYM NOTIN DE_MORGAN_THM H1 stTop NotLimitPointOf xTop;
      eq_tac     [Left] by set;
      MATCH_MP_TAC ExistsTensorInter;
      simplify IN_INTER OPEN_IN_INTER;
      set;
    end;
  qed;
`;;

let Interior_DEF = NewDefinition `;
  ∀α s.  Interior α s =
    {x | s ⊂ topspace α  ∧  ∃t. open_in α t ∧ x ∈ t ∧ t ⊂ s}`;;

let Interior_THM = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Interior α s =  
    {x | s ⊂ topspace α  ∧  ∃t. open_in α t ∧ x ∈ t ∧ t ⊂ s}
  by fol Interior_DEF`;;

let IN_Interior = theorem `;
  ∀α s x.  s ⊂ topspace α  ⇒
    (x ∈ Interior α s  ⇔  ∃t. open_in α t ∧ x ∈ t ∧ t ⊂ s)
  by simplify Interior_THM IN_ELIM_THM`;;

let InteriorEq = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    (open_in α s  ⇔  s = Interior α s)

  proof
    intro_TAC ∀α s, H1;
    rewriteL OPEN_IN_SUBOPEN;
    simplify EXTENSION H1 IN_Interior;
    set;
  qed;
`;;

let InteriorOpen = theorem `;
  ∀α s.  open_in α s  ⇒  Interior α s = s
  by fol OPEN_IN_SUBSET InteriorEq`;;

let InteriorEmpty = theorem `;
  ∀α. Interior α ∅ = ∅
  by fol OPEN_IN_EMPTY EMPTY_SUBSET InteriorOpen`;;

let OpenInterior = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  open_in α (Interior α s)

  proof
    ONCE_REWRITE_TAC OPEN_IN_SUBOPEN;
    fol IN_Interior SUBSET;
  qed;
`;;

let InteriorInterior = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    Interior α  (Interior α s) = Interior α s
  by fol OpenInterior InteriorOpen`;;

let InteriorSubset = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Interior α s ⊂ s

  proof
    intro_TAC ∀α s, H1;
    simplify SUBSET Interior_DEF IN_ELIM_THM;
    fol H1 SUBSET;
  qed;
`;;

let InteriorTopspace = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Interior α s ⊂ topspace α
  by fol SUBSET_TRANS InteriorSubset`;;

let SubsetInterior = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒  s ⊂ t  ⇒
    Interior α s ⊂ Interior α t
  by fol SUBSET_TRANS SUBSET IN_Interior SUBSET`;;

let InteriorMaximal = theorem `;
  ∀α s t.  s ⊂ topspace α  ⇒
    t ⊂ s ∧ open_in α t  ⇒  t ⊂ Interior α s
  by fol SUBSET IN_Interior SUBSET`;;

let InteriorMaximalEq = theorem `;
  ∀s t.  t ⊂ topspace α  ⇒
    open_in α s  ⇒  (s ⊂ Interior α t  ⇔  s ⊂ t)
  by fol InteriorMaximal SUBSET_TRANS InteriorSubset`;;

let InteriorUnique = theorem `;
  ∀α s t.  s ⊂ topspace α  ⇒
    t ⊂ s  ∧  open_in α t ∧  (∀t'. t' ⊂ s ∧ open_in α t' ⇒ t' ⊂ t)
    ⇒ Interior α s = t
  by fol SUBSET_ANTISYM InteriorSubset OpenInterior InteriorMaximal`;;

let OpenSubsetInterior = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒
    open_in α s  ⇒  (s ⊂ Interior α t  ⇔  s ⊂ t)
  by fol InteriorMaximal InteriorSubset SUBSET_TRANS`;;

let InteriorInter = theorem `;
  ∀α s t.  s ⊂ topspace α  ∧  t ⊂ topspace α  ⇒
    Interior α (s ∩ t) = Interior α s ∩ Interior α t

  proof
    intro_TAC ∀α s t, sTop tTop;
    rewrite GSYM SUBSET_ANTISYM_EQ SUBSET_INTER;
    conj_tac     [Left] by fol sTop tTop SubsetInterior INTER_SUBSET;
    s ∩ t ⊂ topspace α     [] by fol sTop INTER_SUBSET SUBSET_TRANS;
    fol - sTop tTop OpenInterior OPEN_IN_INTER InteriorSubset InteriorMaximal INTER_TENSOR;
  qed;
`;;

let InteriorFiniteInters = theorem `;
  ∀α s.  FINITE s ⇒ ¬(s = ∅) ⇒ (∀t. t ∈ s ⇒ t ⊂ topspace α) ⇒
    Interior α (INTERS s) = INTERS (IMAGE (Interior α) s)

  proof
    intro_TAC ∀α;
    MATCH_MP_TAC FINITE_INDUCT;
    rewrite INTERS_INSERT IMAGE_CLAUSES IN_INSERT;
    intro_TAC ∀x s, sCase, xsNonempty, sSetOfSubsets;
    case_split sEmpty | sNonempty by fol;
    suppose s = ∅;
      rewrite INTERS_0 INTER_UNIV IMAGE_CLAUSES sEmpty;
    end;
    suppose ¬(s = ∅);
      simplify INTERS_SUBSET  sSetOfSubsets InteriorInter sNonempty sSetOfSubsets sCase;
    end;
  qed;
`;;

let InteriorIntersSubset = theorem `;
  ∀α f.  ¬(f = ∅) ∧ (∀t. t ∈ f ⇒ t ⊂ topspace α) ⇒
    Interior α (INTERS f)  ⊂  INTERS (IMAGE (Interior α) f)

  proof
    intro_TAC ∀α f, H1 H2;
    INTERS f ⊂ topspace α     [] by set H1 H2;
    simplify SUBSET IN_INTERS FORALL_IN_IMAGE - H2 IN_Interior;
    fol;
  qed;
`;;

let UnionInteriorSubset = theorem `;
  ∀α s t.  s ⊂ topspace α  ∧  t ⊂ topspace α  ⇒
    Interior α s ∪ Interior α t  ⊂  Interior α (s ∪ t)

  proof
    intro_TAC ∀α s t, sTop tTop;
    s ∪ t ⊂ topspace α     [] by fol sTop tTop UNION_SUBSET;
    fol sTop tTop - OpenInterior OPEN_IN_UNION InteriorMaximal UNION_TENSOR InteriorSubset;
  qed;
`;;

let InteriorEqEmpty = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    (Interior α s = ∅  ⇔  ∀t. open_in α t ∧ t ⊂ s  ⇒  t = ∅)
  by fol InteriorMaximal SUBSET_EMPTY OpenInterior SUBSET_REFL InteriorSubset`;;

let InteriorEqEmptyAlt = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    (Interior α s = ∅  ⇔  ∀t. open_in α t ∧ ¬(t = ∅) ⇒ ¬(t ━ s = ∅))

  proof
    simplify InteriorEqEmpty;
    set;
  qed;
`;;

let InteriorUnionsOpenSubsets = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  UNIONS {t | open_in α t ∧ t ⊂ s} = Interior α s

  proof
    intro_TAC ∀α s, H1;
    consider t such that
    t = UNIONS {f | open_in α f ∧ f ⊂ s}     [tDef] by fol;
    t ⊂ s  ∧  ∀f. f ⊂ s ∧ open_in α f ⇒ f ⊂ t     [] by set tDef;
    simplify H1 tDef - OPEN_IN_UNIONS IN_ELIM_THM InteriorUnique;
  qed;
`;;

let InteriorClosedUnionEmptyInterior = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    closed_in α s ∧ Interior α t = ∅  ⇒
    Interior α (s ∪ t) = Interior α s

  proof
    intro_TAC ∀α s t, H1 H2, H3 H4;
    s ∪ t ⊂ topspace α     [stTop] by fol H1 H2 UNION_SUBSET;
    Interior α (s ∪ t) ⊂ s     []
    proof
      simplify SUBSET stTop IN_Interior LEFT_IMP_EXISTS_THM;
      X_genl_TAC y O;     intro_TAC openO yO Os_t;
      consider O' such that O' = (topspace α ━ s) ∩ O     [O'def] by fol -;
      O' ⊂ t     [O't] by set O'def Os_t;
      assume y ∉ s     [yNOTs] by fol - ∉;
      y ∈ topspace α ━ s     [] by fol openO OPEN_IN_SUBSET yO SUBSET yNOTs IN_DIFF ∉;
      y ∈ O'  ∧  open_in α O'     [] by fol O'def - yO IN_INTER H3 closed_in openO OPEN_IN_INTER;
      fol O'def - O't H2 IN_Interior SUBSET MEMBER_NOT_EMPTY H4;
    qed;
    fol SUBSET_ANTISYM H1 stTop OpenInterior - InteriorMaximal SUBSET_UNION SubsetInterior;
  qed;
`;;

let InteriorUnionEqEmpty = theorem `;
  ∀α s t.  s ∪ t ⊂ topspace α  ⇒
    closed_in α s ∨ closed_in α t
    ⇒ (Interior α (s ∪ t) = ∅  ⇔  Interior α s = ∅ ∧ Interior α t = ∅)

  proof
    intro_TAC ∀α s t, H1, H2;
    s ⊂ topspace α ∧ t ⊂ topspace α     [] by fol H1 UNION_SUBSET;
    eq_tac     [Left] by fol - H1 SUBSET_UNION SubsetInterior SUBSET_EMPTY;
    fol UNION_COMM - H2 InteriorClosedUnionEmptyInterior;
  qed;
`;;

let Closure_DEF = NewDefinition `;
  ∀α s.  Closure α s  =  s ∪ LimitPointOf α s`;;

let Closure_THM = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Closure α s  =  s ∪ LimitPointOf α s
  by fol Closure_DEF`;;

let IN_Closure = theorem `;
  ∀α s x.  s ⊂ topspace α  ⇒
    (x ∈ Closure α s  ⇔  x ∈ topspace α ∧
    ∀t. x ∈ t ∧ open_in α t  ⇒  ∃y. y ∈ s ∧ y ∈ t)

  proof
    intro_TAC ∀α s x, H1;
    simplify H1 Closure_THM IN_UNION IN_LimitPointOf;
    fol H1 SUBSET;
  qed;
`;;

let ClosureSubset = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  s ⊂ Closure α s
  by fol SUBSET IN_Closure`;;

let ClosureTopspace = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Closure α s ⊂ topspace α
  by fol SUBSET IN_Closure`;;

let ClosureInterior = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    Closure α s  =  topspace α ━ (Interior α (topspace α ━ s))

  proof
    intro_TAC ∀α s, H1;
    simplify H1 EXTENSION IN_Closure IN_DIFF IN_Interior SUBSET;
    fol OPEN_IN_SUBSET SUBSET;
  qed;
`;;

let InteriorClosure = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    Interior α s = topspace α ━ (Closure α (topspace α ━ s))
  by fol SUBSET_DIFF InteriorTopspace DIFF_REFL ClosureInterior`;;

let ClosedClosure = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  closed_in α (Closure α s)
  by fol closed_in ClosureInterior DIFF_REFL SUBSET_DIFF InteriorTopspace OpenInterior`;;

let SubsetClosure = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒  s ⊂ t  ⇒  Closure α s ⊂ Closure α t

  proof
    intro_TAC ∀α s t, tSubset, st;
    s ⊂ topspace α     [] by fol tSubset st SUBSET_TRANS;
    simplify tSubset - Closure_THM st LimptSubset UNION_TENSOR;
  qed;
`;;

let ClosureHull = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Closure α s = (closed_in α) hull s

  proof
    intro_TAC ∀α s, H1;
    MATCH_MP_TAC GSYM HULL_UNIQUE;
    simplify H1 ClosureSubset ClosedClosure Closure_THM UNION_SUBSET;
    fol LimptSubset CLOSED_IN_SUBSET ClosedLimpt SUBSET_TRANS;
  qed;
`;;

let ClosureEq = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  (Closure α s = s  ⇔  closed_in α s)
  by fol ClosedClosure ClosedLimpt Closure_THM SUBSET_UNION_ABSORPTION UNION_COMM`;;

let ClosureClosed = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  closed_in α s  ⇒  Closure α s = s
  by fol ClosureEq`;;

let ClosureClosure = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Closure α (Closure α s) = Closure α s
  by fol ClosureTopspace ClosureHull HULL_HULL`;;

let ClosureUnion = theorem `;
  ∀α s t.  s ∪ t ⊂ topspace α
    ⇒ Closure α (s ∪ t)  =  Closure α s ∪ Closure α t

  proof
    intro_TAC ∀α s t, H1;
    s ⊂ topspace α ∧ t ⊂ topspace α     [stTop] by fol H1 UNION_SUBSET;
    simplify H1 stTop Closure_THM LimitPointUnion;
    set;
  qed;
`;;

let ClosureInterSubset = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    Closure α (s ∩ t)  ⊂  Closure α s ∩ Closure α t
  by fol SUBSET_INTER INTER_SUBSET SubsetClosure`;;

let ClosureIntersSubset = theorem `;
  ∀α f.  (∀s. s ∈ f ⇒ s ⊂ topspace α)  ⇒
    Closure α (INTERS f)  ⊂  INTERS (IMAGE (Closure α) f)

  proof
    intro_TAC ∀α f, H1;
    rewrite SET_RULE [s ⊂ INTERS f ⇔ ∀t. t ∈ f ⇒ s ⊂ t] FORALL_IN_IMAGE;
    X_genl_TAC s;
    intro_TAC sf;
    s ⊂ topspace α  ∧  INTERS f ⊂ s  ∧  INTERS f ⊂ topspace α     [] by set H1 sf;
    fol SubsetClosure -;
  qed;
`;;

let ClosureMinimal = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒
    s ⊂ t ∧ closed_in α t  ⇒  Closure α s ⊂ t
  by fol SubsetClosure ClosureClosed`;;

let ClosureMinimalEq = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    closed_in α t  ⇒  (Closure α s ⊂ t ⇔ s ⊂ t)
  by fol SUBSET_TRANS ClosureSubset ClosureMinimal`;;

let ClosureUnique = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒
    s ⊂ t ∧ closed_in α t ∧ (∀u. s ⊂ u ∧ closed_in α u  ⇒  t ⊂ u)
    ⇒ Closure α s = t
  by fol SUBSET_ANTISYM_EQ ClosureMinimal SUBSET_TRANS ClosureSubset ClosedClosure`;;

let ClosureEmpty = theorem `;
  Closure α ∅ = ∅
  by fol EMPTY_SUBSET CLOSED_IN_EMPTY ClosureClosed`;;

let ClosureUnions = theorem `;
  ∀α f.  FINITE f  ⇒  (∀ t. t ∈ f ⇒ t ⊂ topspace α)  ⇒
    Closure α (UNIONS f) = UNIONS {Closure α t | t ∈ f}

  proof
    intro_TAC ∀α;
    MATCH_MP_TAC FINITE_INDUCT;
    rewrite UNIONS_0 SET_RULE [{f x | x ∈ ∅} = ∅] ClosureEmpty UNIONS_INSERT
    SET_RULE [{f x | x ∈ a INSERT t} = (f a) INSERT {f x | x ∈ t}] IN_INSERT;
    fol UNION_SUBSET UNIONS_SUBSET IN_UNIONS ClosureUnion;
  qed;
`;;

let ClosureEqEmpty = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  (Closure α s = ∅  ⇔  s = ∅)
  by fol ClosureEmpty ClosureSubset SUBSET_EMPTY`;;

let ClosureSubsetEq = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  (Closure α s ⊂ s  ⇔  closed_in α s)
  by fol ClosureEq ClosureSubset SUBSET_ANTISYM`;;

let OpenInterClosureEqEmpty = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    open_in α s  ⇒  (s ∩ Closure α t = ∅  ⇔  s ∩ t = ∅)

  proof
    intro_TAC ∀α s t, H1 H2, H3;
    eq_tac     [Left] by fol H2 ClosureSubset INTER_TENSOR SUBSET_REFL SUBSET_EMPTY;
    intro_TAC stDisjoint;
    s ⊂ Interior α (topspace α ━ t)     [] by fol H2 SUBSET_DIFF H3 H1 H2 stDisjoint SUBSET_COMPLEMENT OpenSubsetInterior;
    fol H1 H2 InteriorTopspace - COMPLEMENT_DISJOINT H2 ClosureInterior;
  qed;
`;;

let OpenInterClosureSubset = theorem `;
  ∀α s t.  t ⊂ topspace α  ⇒
    open_in α s  ⇒  s ∩ Closure α t ⊂ Closure α (s ∩ t)

  proof
    intro_TAC ∀α s t, tTop, sOpen;
    s ⊂ topspace α     [sTop] by fol OPEN_IN_SUBSET sOpen;
    s ∩ t ⊂ topspace α     [stTop] by fol sTop sTop INTER_SUBSET SUBSET_TRANS;
    simplify tTop - Closure_THM UNION_OVER_INTER SUBSET_UNION SUBSET_UNION;
    s ∩ LimitPointOf α t  ⊂  LimitPointOf α (s ∩ t)     []
    proof
      simplify SUBSET IN_INTER tTop stTop IN_LimitPointOf;
      X_genl_TAC x;     intro_TAC xs xTop xLIMt;
      X_genl_TAC O;     intro_TAC xO Oopen;
      x ∈ O ∩ s  ∧  open_in α (O ∩ s)     [xOsOpen] by fol xs xO IN_INTER Oopen sOpen OPEN_IN_INTER;
      fol xOsOpen xLIMt IN_INTER;
    qed;
    simplify - UNION_TENSOR SUBSET_REFL;
  qed;
`;;

let ClosureOpenInterSuperset = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    open_in α s ∧ s ⊂ Closure α t  ⇒  Closure α (s ∩ t) = Closure α s

  proof
    intro_TAC ∀α s t, sTop tTop, sOpen sSUBtC;
    s ∩ t ⊂ topspace α     [stTop] by fol INTER_SUBSET sTop SUBSET_TRANS;
    MATCH_MP_TAC SUBSET_ANTISYM;
    conj_tac     [Left] by fol sTop INTER_SUBSET SubsetClosure;
    s  ⊂  Closure α (s ∩ t)     [] by fol tTop sOpen OpenInterClosureSubset SUBSET_REFL sSUBtC SUBSET_INTER SUBSET_TRANS;
    fol stTop ClosureTopspace - ClosedClosure ClosureMinimal;
  qed;
`;;

let ClosureComplement = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    Closure α (topspace α ━ s) = topspace α ━ Interior α s
  by fol InteriorClosure SUBSET_DIFF ClosureTopspace DIFF_REFL`;;

let InteriorComplement = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    Interior α (topspace α ━ s) = topspace α ━ Closure α s
  by fol SUBSET_DIFF InteriorTopspace DIFF_REFL ClosureInterior DIFF_REFL`;;

let ClosureInteriorComplement = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    topspace α ━ Closure α (Interior α s)
    = Interior α (Closure α (topspace α ━ s))
  by fol InteriorTopspace InteriorComplement ClosureComplement`;;

let InteriorClosureComplement = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    topspace α ━ Interior α (Closure α s)
    = Closure α (Interior α (topspace α ━ s))
  by fol ClosureTopspace SUBSET_TRANS InteriorComplement ClosureComplement`;;

let ConnectedIntermediateClosure = theorem `;
  ∀α s t.  s ⊂ topspace α  ⇒
    Connected (subtopology α s) ∧  s ⊂ t  ∧  t ⊂ Closure α s
    ⇒ Connected (subtopology α t)

  proof
    intro_TAC ∀α s t, sTop, sCon st tCs;
    t ⊂ topspace α     [tTop] by fol tCs sTop ClosureTopspace SUBSET_TRANS;
    simplify tTop ConnectedSubtopology_ALT;
    X_genl_TAC u v;
    intro_TAC uOpen vOpen t_uv uvtEmpty;
    u ⊂ topspace α  ∧  v ⊂ topspace α     [uvTop] by fol uOpen vOpen OPEN_IN_SUBSET;
    u ∩ s = ∅  ∨  v ∩ s = ∅     [] by fol sTop uvTop uOpen vOpen st t_uv uvtEmpty SUBSET_TRANS SUBSET_REFL INTER_TENSOR SUBSET_EMPTY sCon ConnectedSubtopology_ALT;
    s ⊂ topspace α ━ u  ∨  s ⊂ topspace α ━ v     [] by fol - sTop uvTop INTER_COMM SUBSET_COMPLEMENT;
    t ⊂ topspace α ━ u  ∨  t ⊂ topspace α ━ v     [] by fol SUBSET_DIFF - uvTop uOpen vOpen OPEN_IN_CLOSED_IN ClosureMinimal tCs SUBSET_TRANS;
    fol tTop uvTop - SUBSET_COMPLEMENT INTER_COMM;
  qed;
`;;

let ConnectedClosure = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Connected (subtopology α s) ⇒
    Connected (subtopology α (Closure α s))
  by fol ClosureTopspace ClosureSubset SUBSET_REFL ConnectedIntermediateClosure`;;

let ConnectedUnionStrong = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    Connected (subtopology α s)  ∧  Connected (subtopology α t)  ∧
    ¬(Closure α s ∩ t = ∅)
    ⇒ Connected (subtopology α (s ∪ t))

  proof
    intro_TAC ∀α s t, sTop tTop, H2 H3 H4;
    consider p s' such that
    p ∈ Closure α s  ∧  p ∈ t  ∧  s' = p ╪ s     [pCst] by fol H4 MEMBER_NOT_EMPTY IN_INTER;
    s ⊂ s'  ∧  s' ⊂ Closure α s     [s_ps_Cs] by fol IN_INSERT SUBSET pCst sTop ClosureSubset INSERT_SUBSET;
    Connected (subtopology α (s'))     [s'Con] by fol sTop H2 s_ps_Cs ConnectedIntermediateClosure;
    s ∪ t = s' ∪ t  ∧  ¬(s' ∩ t = ∅)     [] by fol pCst INSERT_UNION IN_INSERT IN_INTER MEMBER_NOT_EMPTY;
    fol s_ps_Cs sTop ClosureTopspace SUBSET_TRANS tTop - s'Con H3 ConnectedUnion;
  qed;
`;;

let InteriorDiff = theorem `;
  ∀α s t.   s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    Interior α (s ━ t) = Interior α s ━ Closure α t
  by fol ClosureTopspace InteriorTopspace COMPLEMENT_INTER_DIFF InteriorComplement SUBSET_DIFF InteriorInter`;;

let ClosedInLimpt = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    (closed_in (subtopology α t) s  ⇔
    s ⊂ t  ∧  LimitPointOf α s ∩ t ⊂ s)

  proof
    intro_TAC ∀α s t, H1 H2;
    simplify H2 ClosedInSubtopology;
    eq_tac     [Right]
    proof
      intro_TAC sSUBt LIMstSUBs;
      exists_TAC Closure α s;
      simplify H1 ClosedClosure Closure_THM INTER_COMM UNION_OVER_INTER;
      set sSUBt LIMstSUBs;
    qed;
    rewrite LEFT_IMP_EXISTS_THM;     X_genl_TAC D;     intro_TAC Dexists;
    LimitPointOf α (D ∩ t) ⊂ D     [] by fol Dexists CLOSED_IN_SUBSET INTER_SUBSET LimptSubset ClosedLimpt SUBSET_TRANS;
    fol Dexists INTER_SUBSET - SUBSET_REFL INTER_TENSOR;
  qed;
`;;

let ClosedInLimpt_ALT = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    (closed_in (subtopology α t) s  ⇔
    s ⊂ t  ∧  ∀x. x ∈ LimitPointOf α s ∧ x ∈ t ⇒ x ∈ s)
  by simplify SUBSET IN_INTER ClosedInLimpt`;;

let ClosedInInterClosure = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    (closed_in (subtopology α s) t  ⇔  s ∩ Closure α t = t)

  proof     simplify Closure_THM ClosedInLimpt;     set;     qed;
`;;

let InteriorClosureIdemp = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    Interior α (Closure α (Interior α (Closure α s)))
    = Interior α (Closure α s)

  proof
    intro_TAC ∀α s, H1;
    consider IC CIC such that
    IC = Interior α (Closure α s)  ∧  CIC = Closure α IC     [CICdef] by fol;
    Closure α s ⊂ topspace α     [Ctop] by fol H1 ClosureTopspace;
    IC ⊂ topspace α     [ICtop] by fol CICdef - H1 InteriorTopspace;
    CIC ⊂ topspace α     [CICtop] by fol CICdef - ClosureTopspace;
    IC ⊂ CIC     [ICsubCIC] by fol CICdef ICtop ClosureSubset;
    ∀u. u ⊂ CIC ∧ open_in α u ⇒ u ⊂ IC     [] by fol CICdef Ctop InteriorSubset SubsetClosure H1 ClosureClosure SUBSET_TRANS OpenSubsetInterior;
    fol CICdef CICtop ICsubCIC Ctop OpenInterior - InteriorUnique;
  qed;
`;;

let InteriorClosureIdemp = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    Interior α (Closure α (Interior α (Closure α s)))
    = Interior α (Closure α s)

  proof
    intro_TAC ∀α s, H1;
    Closure α s ⊂ topspace α     [Ctop] by fol H1 ClosureTopspace;
    consider IC CIC such that
    IC = Interior α (Closure α s)  ∧  CIC = Closure α IC     [ICdefs] by fol;
    IC ⊂ topspace α     [] by fol - Ctop H1 InteriorTopspace;
    CIC ⊂ topspace α  ∧  IC ⊂ CIC  ∧  ∀u. u ⊂ CIC ∧ open_in α u ⇒ u ⊂ IC     [] by fol ICdefs Ctop - ClosureTopspace ClosureSubset InteriorSubset SubsetClosure H1 ClosureClosure SUBSET_TRANS OpenSubsetInterior;
    fol ICdefs - Ctop OpenInterior InteriorUnique;
  qed;
`;;

let ClosureInteriorIdemp = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    Closure α (Interior α (Closure α (Interior α s)))
    = Closure α (Interior α s)

  proof
    intro_TAC ∀α s, H1;
    consider t such that t = topspace α ━ s     [tDef] by fol;
    t ⊂ topspace α  ∧  s = topspace α ━ t     [tProps] by fol - H1 SUBSET_DIFF DIFF_REFL;
    Interior α (Closure α t) ⊂ topspace α     [] by fol - ClosureTopspace InteriorTopspace;
    simplify tProps - GSYM InteriorClosureComplement InteriorClosureIdemp;
  qed;
`;;

let InteriorClosureDiffSpaceEmpty = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Interior α (Closure α s ━ s) = ∅

  proof
    intro_TAC ∀α s, H1;
    Closure α s ━ s ⊂ topspace α     [Cs_sTop] by fol H1 ClosureTopspace SUBSET_DIFF SUBSET_TRANS;
    assume ¬(Interior α (Closure α s ━ s) = ∅)     [Contradiction] by fol -;
    consider x such that
    x ∈ (Interior α (Closure α s ━ s))     [xExists] by fol - MEMBER_NOT_EMPTY;
    consider t such that
    open_in α t ∧ x ∈ t ∧ t ⊂ (s ∪ LimitPointOf α s) ━ s     [tProps] by fol - Cs_sTop IN_Interior Closure_DEF;
    t ⊂ LimitPointOf α s ∧ s ∩ (t ━ {x}) = ∅     [tSubLIMs] by set -;
    x ∈ LimitPointOf α s ∧ x ∉ s     [xLims] by fol tProps - SUBSET IN_DIFF ∉;
    fol H1 xLims IN_LimitPointOf tProps tSubLIMs NotLimitPointOf ∉;
  qed;
`;;

let NowhereDenseUnion = theorem `;
  ∀α s t.  s ∪ t ⊂ topspace α  ⇒
    (Interior α (Closure α (s ∪ t)) = ∅  ⇔
    Interior α (Closure α s) = ∅  ∧  Interior α (Closure α t) = ∅)

  proof
    intro_TAC ∀α s t, H1;
    s ⊂ topspace α ∧ t ⊂ topspace α     [] by fol H1 UNION_SUBSET;
    simplify H1 - ClosureUnion ClosureTopspace UNION_SUBSET ClosedClosure InteriorUnionEqEmpty;
  qed;
`;;

let NowhereDense = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒
    (Interior α (Closure α s) = ∅ ⇔
    ∀t. open_in α t ∧ ¬(t = ∅)  ⇒  
    ∃u. open_in α u ∧ ¬(u = ∅) ∧ u ⊂ t ∧ u ∩ s = ∅)

  proof
    intro_TAC ∀α s, H1;
    simplify H1 ClosureTopspace InteriorEqEmptyAlt;
    eq_tac     [Left]
    proof
      intro_TAC H2;
      X_genl_TAC t;
      intro_TAC tOpen tNonempty;
      exists_TAC t ━ Closure α s;
      fol tOpen H1 ClosedClosure OPEN_IN_DIFF tOpen tNonempty H2 SUBSET_DIFF H1 ClosureSubset SET_RULE [∀s t A.  s ⊂ t  ⇒  (A ━ t) ∩ s = ∅];
    qed;
    intro_TAC H2;
    X_genl_TAC t;
    intro_TAC tOpen tNonempty;
    consider u such that
    open_in α u ∧ ¬(u = ∅) ∧ u ⊂ t ∧ u ∩ s = ∅     [uExists] by simplify tOpen tNonempty H2;
    MP_TAC ISPECL [α; u; s] OpenInterClosureEqEmpty;
    simplify uExists OPEN_IN_SUBSET H1;
    set uExists;
  qed;
`;;

let InteriorClosureInterOpen = theorem `;
  ∀α s t.  open_in α s ∧ open_in α t  ⇒
    Interior α (Closure α (s ∩ t)) =
    Interior α (Closure α s) ∩ Interior α (Closure α t)

  proof
    intro_TAC ∀α s t, sOpen tOpen;
    s ⊂ topspace α     [sTop] by fol sOpen OPEN_IN_SUBSET;
    t ⊂ topspace α     [tTop] by fol tOpen OPEN_IN_SUBSET;
    rewrite SET_RULE [∀s t u. u = s ∩ t  ⇔  s ∩ t ⊂ u ∧ u ⊂ s ∧ u ⊂ t];
    simplify sTop tTop INTER_SUBSET SubsetClosure ClosureTopspace SubsetInterior;
    s ∩ t ⊂ topspace α     [stTop] by fol INTER_SUBSET sTop SUBSET_TRANS;
    Closure α s ⊂ topspace α  ∧  Closure α t ⊂ topspace α  [CsCtTop] by fol sTop tTop ClosureTopspace;
    Closure α s ∩ Closure α t ⊂ topspace α     [CsIntCtTop] by fol - INTER_SUBSET SUBSET_TRANS;
    Closure α s ━ s ∪ Closure α t ━ t  ⊂  topspace α     [Cs_sUNIONCt_tTop] by fol CsCtTop SUBSET_DIFF UNION_SUBSET SUBSET_TRANS;
    simplify CsCtTop GSYM InteriorInter;
    Interior α (Closure α s ∩ Closure α t) ⊂ Closure α (s ∩ t)     []
    proof
      simplify CsIntCtTop InteriorTopspace ISPECL [topspace α] COMPLEMENT_DISJOINT stTop ClosureTopspace GSYM ClosureComplement GSYM InteriorComplement CsIntCtTop SUBSET_DIFF GSYM InteriorInter;
      closed_in α (Closure α s ━ s) ∧ closed_in α (Closure α t ━ t)     [] by fol sTop tTop ClosedClosure sOpen tOpen CLOSED_IN_DIFF;
      Interior α (Closure α s ━ s ∪ Closure α t ━ t) = ∅     [IntEmpty] by fol Cs_sUNIONCt_tTop - sTop tTop InteriorClosureDiffSpaceEmpty InteriorUnionEqEmpty;
      Closure α s ∩ Closure α t ∩ (topspace α ━ (s ∩ t))  ⊂
      Closure α s ━ s ∪ Closure α t ━ t     [] by set;
      fol Cs_sUNIONCt_tTop - SubsetInterior IntEmpty INTER_ACI SUBSET_EMPTY;
    qed;
    fol stTop ClosureTopspace - CsIntCtTop OpenInterior InteriorMaximal;
  qed;
`;;

let ClosureInteriorUnionClosed = theorem `;
  ∀α s t.   closed_in α s ∧ closed_in α t ⇒
    Closure α (Interior α (s ∪ t))  =
    Closure α (Interior α s) ∪ Closure α (Interior α t)

  proof
    rewrite closed_in;
    intro_TAC ∀α s t, sClosed tClosed;
    simplify sClosed tClosed ClosureTopspace UNION_SUBSET InteriorTopspace ISPECL [topspace α] COMPLEMENT_DUALITY_UNION;
    simplify sClosed tClosed UNION_SUBSET ClosureTopspace InteriorTopspace ClosureInteriorComplement DIFF_UNION SUBSET_DIFF InteriorClosureInterOpen;
  qed;
`;;

let RegularOpenInter = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    Interior α (Closure α s) = s ∧ Interior α (Closure α t) = t
    ⇒ Interior α (Closure α (s ∩ t)) = s ∩ t
  by fol ClosureTopspace OpenInterior InteriorClosureInterOpen`;;

let RegularClosedUnion = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    Closure α (Interior α s) = s  ∧  Closure α (Interior α t) = t
    ⇒ Closure α (Interior α (s ∪ t)) = s ∪ t
  by fol InteriorTopspace ClosureInteriorUnionClosed ClosedClosure`;;

let DiffClosureSubset = theorem `;
  ∀α s t.  s ⊂ topspace α ∧ t ⊂ topspace α  ⇒
    Closure α s ━ Closure α t ⊂ Closure α (s ━ t)

  proof
    intro_TAC ∀α s t, sTop tTop;
    Closure α s ━ Closure α t ⊂ Closure α (s ━ Closure α t)     [] by fol sTop ClosureTopspace tTop ClosedClosure tTop closed_in OpenInterClosureSubset INTER_COMM COMPLEMENT_INTER_DIFF;
    fol - tTop ClosureSubset SUBSET_DUALITY sTop SUBSET_DIFF SUBSET_TRANS SubsetClosure;
  qed;
`;;

let Frontier_DEF = NewDefinition `;
  ∀α s.  Frontier α s = (Closure α s) ━ (Interior α s)`;;

let Frontier_THM = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  Frontier α s = (Closure α s) ━ (Interior α s)
  by fol Frontier_DEF`;;

let FrontierClosed = theorem `;
  ∀α s.  s ⊂ topspace α  ⇒  closed_in α (Frontier α s)
  by simplify Frontier_THM ClosedClosure OpenInterior CLOSED_IN_DIFF`;;

let FrontierClosures = theorem `;
  ∀s.  s ⊂ topspace α  ⇒
    Frontier α s  =  (Closure α s) ∩ (Closure α (topspace α ━ s))
  by simplify SET_RULE [∀A s t.  s ⊂ A ∧ t ⊂ A   ⇒  s ━ (A ━ t) = s ∩ t] Frontier_THM InteriorClosure ClosureTopspace SUBSET_DIFF`;;

(* ------------------------------------------------------------------------- *)
(* The universal Euclidean versions are what we use most of the time.        *)
(* ------------------------------------------------------------------------- *)

let open_def = NewDefinition `;
  open s  ⇔  ∀x. x ∈ s ⇒ ∃e. &0 < e ∧ ∀x'. dist(x',x) < e ⇒ x' ∈ s`;;

let closed = NewDefinition `;
  closed s ⇔ open (UNIV ━ s)`;;

let euclidean = new_definition
 `euclidean = mk_topology (UNIV, open)`;;

let OPEN_EMPTY = theorem `;
  open ∅
  by rewrite open_def NOT_IN_EMPTY`;;

let OPEN_UNIV = theorem `;
  open UNIV
  by fol open_def IN_UNIV REAL_LT_01`;;

let OPEN_INTER = theorem `;
  ∀s t. open s ∧ open t ⇒ open (s ∩ t)

  proof
    intro_TAC ∀s t, sOpen tOpen;
    rewrite open_def IN_INTER;
    intro_TAC ∀x, xs xt;
    consider d1 such that
    &0 < d1 ∧ ∀x'. dist (x',x) < d1 ⇒ x' ∈ s     [d1Exists] by fol sOpen xs open_def;
    consider d2 such that
    &0 < d2 ∧ ∀x'. dist (x',x) < d2 ⇒ x' ∈ t     [d2Exists] by fol tOpen xt open_def;
    consider e such that &0 < e /\ e < d1 /\ e < d2     [eExists] by fol d1Exists d2Exists REAL_DOWN2;
    fol - d1Exists d2Exists REAL_LT_TRANS;
  qed;
`;;

let OPEN_UNIONS = theorem `;
  (∀s. s ∈ f ⇒ open s)  ⇒  open(UNIONS f)
  by fol open_def IN_UNIONS`;;

let IstopologyEuclidean = theorem `;
    istopology (UNIV, open)
    by simplify istopology IN IN_UNIV SUBSET OPEN_EMPTY OPEN_UNIV OPEN_INTER OPEN_UNIONS`;;

let OPEN_IN = theorem `;
  open  =  open_in euclidean
  by fol euclidean topology_tybij IstopologyEuclidean TopologyPAIR PAIR_EQ`;;

let TOPSPACE_EUCLIDEAN = theorem `;
  topspace euclidean = UNIV
  by fol euclidean IstopologyEuclidean topology_tybij TopologyPAIR PAIR_EQ`;;

let OPEN_EXISTS_IN = theorem `;
  ∀P Q.  (∀a. P a ⇒ open {x | Q a x})  ⇒  open {x | ∃a. P a ∧ Q a x}
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN OPEN_IN_EXISTS_IN`;;

let OPEN_EXISTS = theorem `;
  ∀Q.  (∀a. open {x | Q a x})  ⇒  open {x | ∃a. Q a x}

  proof
    intro_TAC ∀Q;
    (∀a. T ⇒ open {x | Q a x}) ⇒ open {x | ∃a. T ∧ Q a x} [] by simplify OPEN_EXISTS_IN;
    MP_TAC -;
    fol;
  qed;
`;;

let TOPSPACE_EUCLIDEAN_SUBTOPOLOGY = theorem `;
 ∀s. topspace (subtopology euclidean s) = s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN TopspaceSubtopology`;;

let OPEN_IN_REFL = theorem `;
  ∀s. open_in (subtopology euclidean s) s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN OpenInRefl`;;

let CLOSED_IN_REFL = theorem `;
  ∀s. closed_in (subtopology euclidean s) s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN ClosedInRefl`;;

let CLOSED_IN = theorem `;
  ∀s. closed  =  closed_in euclidean
  by fol closed closed_in TOPSPACE_EUCLIDEAN OPEN_IN SUBSET_UNIV EXTENSION IN`;;

let OPEN_UNION = theorem `;
  ∀s t.  open s ∧ open t  ⇒  open(s ∪ t)
  by fol OPEN_IN OPEN_IN_UNION`;;

let OPEN_SUBOPEN = theorem `;
  ∀s. open s ⇔ ∀x. x ∈ s ⇒ ∃t. open t ∧ x ∈ t ∧ t ⊂ s
  by fol OPEN_IN OPEN_IN_SUBOPEN`;;

let CLOSED_EMPTY = theorem `;
  closed ∅
  by fol CLOSED_IN CLOSED_IN_EMPTY`;;

let CLOSED_UNIV = theorem `;
  closed UNIV
  by fol CLOSED_IN TOPSPACE_EUCLIDEAN CLOSED_IN_TOPSPACE`;;

let CLOSED_UNION = theorem `;
  ∀s t.  closed s ∧ closed t  ⇒  closed(s ∪ t)
  by fol CLOSED_IN CLOSED_IN_UNION`;;

let CLOSED_INTER = theorem `;
  ∀s t.  closed s ∧ closed t  ⇒  closed(s ∩ t)
  by fol CLOSED_IN CLOSED_IN_INTER`;;

let CLOSED_INTERS = theorem `;
  ∀f. (∀s. s ∈ f ⇒ closed s)  ⇒  closed (INTERS f)
  by fol CLOSED_IN CLOSED_IN_INTERS INTERS_0 CLOSED_UNIV`;;

let CLOSED_FORALL_IN = theorem `;
  ∀P Q.  (∀a. P a ⇒ closed {x | Q a x})
    ⇒  closed {x | ∀a. P a ⇒ Q a x}

  proof
    intro_TAC ∀P Q;
    case_split Pnonempty | Pempty by fol;
    suppose ¬(P = ∅);
      simplify CLOSED_IN Pnonempty CLOSED_IN_FORALL_IN;
    end;
    suppose P = ∅;
      {x | ∀a. P a ⇒ Q a x} = UNIV     [] by set Pempty;
      simplify - CLOSED_UNIV;
    end;
  qed;
`;;

let CLOSED_FORALL = theorem `;
  ∀Q. (∀a. closed {x | Q a x}) ⇒ closed {x | ∀a. Q a x}

  proof
    intro_TAC ∀Q;
    (∀a. T ⇒ closed {x | Q a x}) ⇒ closed {x | ∀a. T ⇒ Q a x} [] by simplify CLOSED_FORALL_IN;
    MP_TAC -;
    fol;
  qed;
`;;

let OPEN_CLOSED = theorem `;
  ∀s.  open s  ⇔  closed(UNIV ━ s)
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN CLOSED_IN OPEN_IN_CLOSED_IN`;;

let OPEN_DIFF = theorem `;
  ∀s t.  open s ∧ closed t  ⇒  open(s ━ t)
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN CLOSED_IN OPEN_IN_DIFF`;;

let CLOSED_DIFF = theorem `;
  ∀s t.  closed s ∧ open t  ⇒  closed (s ━ t)
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN CLOSED_IN CLOSED_IN_DIFF`;;

let OPEN_INTERS = theorem `;
  ∀s.  FINITE s ∧ (∀t. t ∈ s ⇒ open t)  ⇒  open (INTERS s)
  by fol OPEN_IN OPEN_IN_INTERS INTERS_0 OPEN_UNIV`;;

let CLOSED_UNIONS = theorem `;
  ∀s.  FINITE s ∧ (∀t. t ∈ s ⇒ closed t)  ⇒  closed (UNIONS s)
  by fol CLOSED_IN CLOSED_IN_UNIONS`;;

(* ------------------------------------------------------------------------- *)
(* Open and closed balls and spheres.                                        *)
(* ------------------------------------------------------------------------- *)

let ball = new_definition
  `ball(x,e) = {y | dist(x,y) < e}`;;

let cball = new_definition
  `cball(x,e) = {y | dist(x,y) <= e}`;;

let IN_BALL = theorem `;
 ∀x y e. y ∈ ball(x,e)  ⇔  dist(x,y) < e
  by rewrite ball IN_ELIM_THM`;;

let IN_CBALL = theorem `;
  ∀x y e. y ∈ cball(x, e)  ⇔  dist(x, y) <= e
  by rewrite cball IN_ELIM_THM`;;

let BALL_SUBSET_CBALL = theorem `;
  ∀x e. ball (x,e) ⊂ cball (x, e)

  proof
     rewrite IN_BALL IN_CBALL SUBSET;
     real_arithmetic;
  qed;
`;;

let OPEN_BALL = theorem `;
  ∀x e. open (ball (x,e))

  proof
    rewrite open_def ball IN_ELIM_THM;
    rewrite MESON [DIST_SYM] [∀z. dist (z, y) = dist (y, z)];
    fol REAL_SUB_LT REAL_LT_SUB_LADD REAL_ADD_SYM REAL_LET_TRANS DIST_TRIANGLE;
  qed;
`;;

let CENTRE_IN_BALL = theorem `;
  ∀x e. x ∈ ball(x,e)  ⇔  &0 < e
  by fol IN_BALL DIST_REFL`;;

let OPEN_CONTAINS_BALL = theorem `;
  ∀s. open s  ⇔  ∀x. x ∈ s ⇒ ∃e. &0 < e ∧ ball(x,e) ⊂ s
  by rewrite open_def SUBSET IN_BALL DIST_SYM`;;

let HALF_CBALL_IN_BALL = theorem `;
  ∀e. &0 < e  ⇒  &0 < e/ &2 ∧ e / &2 < e ∧ cball (x, e/ &2) ⊂ ball (x, e)

  proof
    intro_TAC ∀e, H1;
     &0 < e/ &2  ∧  e / &2 < e     [] by real_arithmetic H1;
     fol - SUBSET IN_CBALL IN_BALL REAL_LET_TRANS;
  qed;
`;;

let OPEN_IN_CONTAINS_CBALL_LEMMA = theorem `;
  ∀t s x.  x ∈ s  ⇒
    ((∃e. &0 < e ∧ ball (x, e) ∩ t ⊂ s) ⇔
    (∃e. &0 < e ∧ cball (x, e) ∩ t ⊂ s))
  by fol BALL_SUBSET_CBALL HALF_CBALL_IN_BALL INTER_TENSOR SUBSET_REFL SUBSET_TRANS`;;

(* ------------------------------------------------------------------------- *)
(* Basic "localization" results are handy for connectedness.                 *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_OPEN = theorem `;
  ∀s u.  open_in (subtopology euclidean u) s  ⇔  ∃t. open t ∧ (s = u ∩ t)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN OpenInSubtopology INTER_COMM`;;

let OPEN_IN_INTER_OPEN = theorem `;
  ∀s t u.  open_in (subtopology euclidean u) s  ∧  open t
    ⇒ open_in (subtopology euclidean u) (s ∩ t)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN OpenInSubtopologyInterOpen`;;

let OPEN_IN_OPEN_INTER = theorem `;
  ∀u s.  open s  ⇒  open_in (subtopology euclidean u) (u ∩ s)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN OpenInOpenInter`;;

let OPEN_OPEN_IN_TRANS = theorem `;
  ∀s t.  open s  ∧  open t  ∧  t ⊂ s
    ⇒ open_in (subtopology euclidean s) t
  by fol OPEN_IN OpenOpenInTrans`;;

let OPEN_SUBSET = theorem `;
  ∀s t.  s ⊂ t  ∧  open s  ⇒  open_in (subtopology euclidean t) s
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN OpenSubset`;;

let CLOSED_IN_CLOSED = theorem `;
  ∀s u.
    closed_in (subtopology euclidean u) s  ⇔  ∃t. closed t ∧ (s = u ∩ t)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN ClosedInSubtopology INTER_COMM`;;

let CLOSED_SUBSET_EQ = theorem `;
  ∀u s.  closed s  ⇒  (closed_in (subtopology euclidean u) s  ⇔  s ⊂ u)
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN ClosedSubsetEq`;;

let CLOSED_IN_INTER_CLOSED = theorem `;
  ∀s t u.  closed_in (subtopology euclidean u) s  ∧  closed t
    ⇒ closed_in (subtopology euclidean u) (s ∩ t)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN ClosedInInterClosed`;;

let CLOSED_IN_CLOSED_INTER = theorem `;
  ∀u s. closed s  ⇒  closed_in (subtopology euclidean u) (u ∩ s)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN ClosedInClosedInter`;;

let CLOSED_SUBSET = theorem `;
  ∀s t.  s ⊂ t ∧ closed s  ⇒  closed_in (subtopology euclidean t) s
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN ClosedSubset`;;

let OPEN_IN_SUBSET_TRANS = theorem `;
  ∀s t u.  open_in (subtopology euclidean u) s  ∧  s ⊂ t  ∧  t ⊂ u
    ⇒ open_in (subtopology euclidean t) s
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN OpenInSubsetTrans`;;

let CLOSED_IN_SUBSET_TRANS = theorem `;
  ∀s t u.  closed_in (subtopology euclidean u) s  ∧  s ⊂ t  ∧  t ⊂ u
    ⇒ closed_in (subtopology euclidean t) s
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN ClosedInSubsetTrans`;;

let OPEN_IN_CONTAINS_BALL_LEMMA = theorem `;
  ∀t s x.  x ∈ s  ⇒
    ((∃E. open E  ∧  x ∈ E  ∧  E ∩ t ⊂ s)  ⇔
    (∃e. &0 < e  ∧  ball (x,e) ∩ t ⊂ s))

  proof
    intro_TAC ∀ t s x, xs;
    eq_tac     [Right] by fol CENTRE_IN_BALL OPEN_BALL;
    intro_TAC H2;
    consider a such that
    open a ∧ x ∈ a ∧ a ∩ t ⊂ s     [aExists] by fol H2;
    consider e such that
    &0 < e ∧ ball(x,e) ⊂ a     [eExists] by fol - OPEN_CONTAINS_BALL;
    fol aExists - INTER_SUBSET GSYM SUBSET_INTER SUBSET_TRANS;
  qed;
`;;

let OPEN_IN_CONTAINS_BALL = theorem `;
  ∀s t.  open_in (subtopology euclidean t) s  ⇔
    s ⊂ t  ∧  ∀x. x ∈ s ⇒ ∃e. &0 < e ∧ ball(x,e) ∩ t ⊂ s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN SubtopologyOpenInSubopen GSYM OPEN_IN GSYM OPEN_IN_CONTAINS_BALL_LEMMA`;;

let OPEN_IN_CONTAINS_CBALL = theorem `;
  ∀s t.  open_in (subtopology euclidean t) s  ⇔
    s ⊂ t  ∧  ∀x. x ∈ s ⇒ ∃e. &0 < e ∧ cball(x,e) ∩ t ⊂ s
  by fol OPEN_IN_CONTAINS_BALL OPEN_IN_CONTAINS_CBALL_LEMMA`;;

let open_in = theorem `;
  ∀u s.  open_in (subtopology euclidean u) s   ⇔
    s ⊂ u  ∧
    ∀x. x ∈ s ⇒ ∃e. &0 < e ∧
    ∀x'. x' ∈ u ∧ dist(x',x) < e ⇒ x' ∈ s
  by rewrite OPEN_IN_CONTAINS_BALL IN_INTER SUBSET IN_BALL CONJ_SYM DIST_SYM`;;

(* ------------------------------------------------------------------------- *)
(* These "transitivity" results are handy too.                               *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_TRANS = theorem `;
  ∀s t u. open_in (subtopology euclidean t) s  ∧
    open_in (subtopology euclidean u) t
    ⇒ open_in (subtopology euclidean u) s

  proof
    intro_TAC ∀s t u;
    t ⊂ topspace euclidean  ∧  u ⊂ topspace euclidean     [] by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN;
    fol - OPEN_IN OpenInTrans;
  qed;
`;;

let OPEN_IN_TRANS_EQ = theorem `;
  ∀s t.  (∀u. open_in (subtopology euclidean t) u
    ⇒  open_in (subtopology euclidean s) t)
    ⇔  open_in (subtopology euclidean s) t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN OpenInTransEq`;;

let OPEN_IN_OPEN_TRANS = theorem `;
  ∀u s.  open_in (subtopology euclidean u) s ∧ open u  ⇒  open s

  proof
    intro_TAC ∀u s, H1;
    u ⊂ topspace euclidean     [] by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN;
    fol - H1 OPEN_IN OpenInOpenTrans;
  qed;
`;;

let CLOSED_IN_TRANS = theorem `;
  ∀s t u.  closed_in (subtopology euclidean t) s  ∧
    closed_in (subtopology euclidean u) t
    ⇒ closed_in (subtopology euclidean u) s

  proof
    intro_TAC ∀s t u;
    t ⊂ topspace euclidean ∧ u ⊂ topspace euclidean     [] by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN;
    fol - ClosedInSubtopologyTrans;
  qed;
`;;

let CLOSED_IN_TRANS_EQ = theorem `;
  ∀s t.
    (∀u. closed_in (subtopology euclidean t) u ⇒ closed_in (subtopology euclidean s) t)
    ⇔ closed_in (subtopology euclidean s) t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN ClosedInSubtopologyTransEq`;;

let CLOSED_IN_CLOSED_TRANS = theorem `;
  ∀s u. closed_in (subtopology euclidean u) s ∧ closed u ⇒ closed s

  proof
    intro_TAC ∀u s;
    u ⊂ topspace euclidean     [] by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN;
    fol - CLOSED_IN ClosedInClosedTrans;
  qed;
`;;

let OPEN_IN_SUBTOPOLOGY_INTER_SUBSET = theorem `;
  ∀s u v. open_in (subtopology euclidean u) (u ∩ s)  ∧  v ⊂ u
    ⇒ open_in (subtopology euclidean v) (v ∩ s)
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN OpenInSubtopologyInterSubset`;;

let OPEN_IN_OPEN_EQ = theorem `;
  ∀s t.  open s  ⇒  (open_in (subtopology euclidean s) t ⇔ open t ∧ t ⊂ s)
  by fol OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN OpenInOpenEq`;;

let CLOSED_IN_CLOSED_EQ = theorem `;
  ∀s t.  closed s  ⇒
    (closed_in (subtopology euclidean s) t ⇔ closed t ∧ t ⊂ s)
  by fol CLOSED_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN ClosedInClosedEq`;;

(* ------------------------------------------------------------------------- *)
(* Also some invariance theorems for relative topology.                      *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_INJECTIVE_LINEAR_IMAGE = theorem `;
  ∀f s t.  linear f ∧ (∀x y. f x = f y ⇒ x = y) ⇒ 
    (open_in (subtopology euclidean (IMAGE f t)) (IMAGE f s) ⇔
    open_in (subtopology euclidean t) s)

  proof
    rewrite open_in FORALL_IN_IMAGE IMP_CONJ SUBSET;
    intro_TAC ∀f s t, H1, H2;
    ∀x s. f x ∈ IMAGE f s ⇔ x ∈ s     [fInjMap] by set H2;
    rewrite -;
    ∀x y. f x - f y = f (x - y)     [fSubLinear] by fol H1 LINEAR_SUB;
    consider B1 such that
    &0 < B1  ∧  ∀x. norm (f x) <= B1 * norm x     [B1exists] by fol H1 LINEAR_BOUNDED_POS;
    consider B2 such that
    &0 < B2  ∧  ∀x. norm x * B2 <= norm (f x)     [B2exists] by fol H1 H2 LINEAR_INJECTIVE_BOUNDED_BELOW_POS;
    AP_TERM_TAC;
    eq_tac     [Left]
    proof
      intro_TAC H3, ∀x, xs;
      consider e such that
      &0 < e  ∧  ∀x'. x' ∈ t ⇒ dist (f x',f x) < e ⇒ x' ∈ s     [eExists] by fol H3 xs;
      exists_TAC e / B1;
      simplify REAL_LT_DIV eExists B1exists;
      intro_TAC ∀x', x't;
      ∀x. norm(f x) <= B1 * norm(x)  ∧ norm(x) * B1 < e  ⇒  norm(f x) < e     [normB1] by real_arithmetic;
      simplify fSubLinear B1exists H3 eExists x't normB1 dist REAL_LT_RDIV_EQ;
    qed;
    intro_TAC H3, ∀x, xs;
    consider e such that
    &0 < e  ∧  ∀x'. x' ∈ t ⇒ dist (x',x) < e ⇒ x' ∈ s     [eExists] by fol H3 xs;
    exists_TAC e * B2;
    simplify REAL_LT_MUL eExists B2exists;
    intro_TAC ∀x', x't;
    ∀x. norm x <= norm (f x) / B2 ∧ norm(f x) / B2 < e  ⇒  norm x < e     [normB2] by real_arithmetic;
    simplify fSubLinear B2exists H3 eExists x't normB2 dist REAL_LE_RDIV_EQ REAL_LT_LDIV_EQ;
  qed;
`;;

add_linear_invariants [OPEN_IN_INJECTIVE_LINEAR_IMAGE];;

let CLOSED_IN_INJECTIVE_LINEAR_IMAGE = theorem `;
  ∀f s t. linear f ∧ (∀x y. f x = f y ⇒ x = y)  ⇒
    (closed_in (subtopology euclidean (IMAGE f t)) (IMAGE f s)  ⇔
    closed_in (subtopology euclidean t) s)

  proof
    rewrite closed_in TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
    GEOM_TRANSFORM_TAC[];
  qed;
`;;

add_linear_invariants [CLOSED_IN_INJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Subspace topology results only proved for Euclidean space.                *)
(* ------------------------------------------------------------------------- *)

(* ISTOPLOGY_SUBTOPOLOGY can not be proved, as the definition of topology    *)
(* there is different from the one here.                                     *)

let OPEN_IN_SUBTOPOLOGY = theorem `;
  ∀u s.  open_in (subtopology euclidean u) s  ⇔
    ∃t. open_in euclidean t ∧ s = t ∩ u
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN OpenInSubtopology`;;

let TOPSPACE_SUBTOPOLOGY = theorem `;
  ∀u.  topspace(subtopology euclidean u) = topspace euclidean ∩ u

  proof
    intro_TAC ∀u;
    u ⊂ topspace euclidean     [] by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN;
    fol - TopspaceSubtopology INTER_COMM SUBSET_INTER_ABSORPTION;
  qed;
`;;

let CLOSED_IN_SUBTOPOLOGY = theorem `;
  ∀u s. closed_in (subtopology euclidean u) s  ⇔
  ∃t. closed_in euclidean t ∧ s = t ∩ u
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closed_in ClosedInSubtopology`;;

let OPEN_IN_SUBTOPOLOGY_REFL = theorem `;
  ∀u. open_in (subtopology euclidean u) u  ⇔  u ⊂ topspace euclidean
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN OPEN_IN_REFL`;;

let CLOSED_IN_SUBTOPOLOGY_REFL = theorem `;
  ∀u. closed_in (subtopology euclidean u) u  ⇔  u ⊂ topspace euclidean
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN_REFL`;;

let SUBTOPOLOGY_UNIV = theorem `;
  subtopology euclidean UNIV = euclidean

  proof
    rewrite GSYM Topology_Eq;
    conj_tac     [Left] by fol TOPSPACE_EUCLIDEAN TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
    rewrite GSYM OPEN_IN OPEN_IN_OPEN INTER_UNIV;
    fol;
  qed;
`;;

let SUBTOPOLOGY_SUPERSET = theorem `;
  ∀s.  topspace euclidean ⊂ s  ⇒  subtopology euclidean s = euclidean
  by simplify TOPSPACE_EUCLIDEAN UNIV_SUBSET SUBTOPOLOGY_UNIV`;;

let OPEN_IN_IMP_SUBSET = theorem `;
  ∀s t.  open_in (subtopology euclidean s) t  ⇒  t ⊂ s
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN OpenInImpSubset`;;

let CLOSED_IN_IMP_SUBSET = theorem `;
  ∀s t.  closed_in (subtopology euclidean s) t  ⇒  t ⊂ s
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN ClosedInImpSubset`;;

let OPEN_IN_SUBTOPOLOGY_UNION = theorem `;
  ∀s t u.  open_in (subtopology euclidean t) s  ∧
    open_in (subtopology euclidean u) s
    ⇒  open_in (subtopology euclidean (t ∪ u)) s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN OpenInSubtopologyUnion`;;

let CLOSED_IN_SUBTOPOLOGY_UNION = theorem `;
  ∀s t u.  closed_in (subtopology euclidean t) s  ∧
    closed_in (subtopology euclidean u) s
    ⇒  closed_in (subtopology euclidean (t ∪ u)) s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN ClosedInSubtopologyUnion`;;

(* ------------------------------------------------------------------------- *)
(* Connectedness.                                                            *)
(* ------------------------------------------------------------------------- *)

let connected_DEF = NewDefinition `;
  connected s  ⇔  Connected (subtopology euclidean s)`;;

let connected = theorem `;
  ∀s.  connected s  ⇔  ¬(∃e1 e2.
    open e1  ∧  open e2  ∧  s ⊂ e1 ∪ e2  ∧
    e1 ∩ e2 ∩ s = ∅  ∧  ¬(e1 ∩ s = ∅)  ∧  ¬(e2 ∩ s = ∅))
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN connected_DEF OPEN_IN ConnectedSubtopology`;;

let CONNECTED_CLOSED = theorem `;
  ∀s.  connected s ⇔
    ¬(∃e1 e2. closed e1  ∧  closed e2  ∧  s ⊂ e1 ∪ e2  ∧
    e1 ∩ e2 ∩ s = ∅  ∧  ¬(e1 ∩ s = ∅)  ∧  ¬(e2 ∩ s = ∅))
  by simplify connected_DEF CLOSED_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN connected_DEF CLOSED_IN ConnectedClosedSubtopology`;;

let CONNECTED_OPEN_IN = theorem `;
  ∀s. connected s  ⇔  ¬(∃e1 e2.
    open_in (subtopology euclidean s) e1 ∧
    open_in (subtopology euclidean s) e2 ∧
    s ⊂ e1 ∪ e2  ∧  e1 ∩ e2 = ∅  ∧  ¬(e1 = ∅)  ∧  ¬(e2 = ∅))
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN connected_DEF OPEN_IN ConnectedOpenIn`;;

let CONNECTED_OPEN_IN_EQ = theorem `;
  ∀s. connected s  ⇔  ¬(∃e1 e2.
    open_in (subtopology euclidean s) e1 ∧
    open_in (subtopology euclidean s) e2 ∧
    e1 ∪ e2 = s ∧ e1 ∩ e2 = ∅ ∧
    ¬(e1 = ∅) ∧ ¬(e2 = ∅))

  proof
    simplify connected_DEF Connected_DEF SUBSET_UNIV TOPSPACE_EUCLIDEAN TopspaceSubtopology;
    fol;
  qed;
`;;

let CONNECTED_CLOSED_IN = theorem `;
  ∀s. connected s  ⇔  ¬(∃e1 e2.
    closed_in (subtopology euclidean s) e1 ∧
    closed_in (subtopology euclidean s) e2 ∧
    s ⊂ e1 ∪ e2  ∧  e1 ∩ e2 = ∅  ∧  ¬(e1 = ∅)  ∧  ¬(e2 = ∅))
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN connected_DEF CLOSED_IN ConnectedClosedIn`;;

let CONNECTED_CLOSED_IN_EQ = theorem `;
  ∀s. connected s  ⇔  ¬(∃e1 e2.
    closed_in (subtopology euclidean s) e1  ∧
    closed_in (subtopology euclidean s) e2  ∧
    e1 ∪ e2 = s  ∧  e1 ∩ e2 = ∅  ∧  ¬(e1 = ∅)  ∧  ¬(e2 = ∅))

  proof
    simplify connected_DEF ConnectedClosed SUBSET_UNIV TOPSPACE_EUCLIDEAN TopspaceSubtopology;
    fol;
  qed;
`;;

let CONNECTED_CLOPEN = theorem `;
  ∀s. connected s  ⇔
    ∀t. open_in (subtopology euclidean s) t  ∧
      closed_in (subtopology euclidean s) t ⇒ t = ∅ ∨ t = s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN connected_DEF ConnectedClopen TopspaceSubtopology`;;

let CONNECTED_CLOSED_SET = theorem `;
  ∀s.  closed s ⇒
    (connected s  ⇔
    ¬(∃e1 e2. closed e1 ∧ closed e2 ∧
    ¬(e1 = ∅)  ∧  ¬(e2 = ∅)  ∧  e1 ∪ e2 = s  ∧  e1 ∩ e2 = ∅))
  by simplify connected_DEF CLOSED_IN  closed_in ConnectedClosedSet`;;

let CONNECTED_OPEN_SET = theorem `;
  ∀s.  open s  ⇒
    (connected s ⇔
    ¬(∃e1 e2.  open e1  ∧  open e2  ∧
    ¬(e1 = ∅)  ∧  ¬(e2 = ∅)  ∧  e1 ∪ e2 = s  ∧  e1 ∩ e2 = ∅))
  by simplify connected_DEF OPEN_IN ConnectedOpenSet`;;

let CONNECTED_EMPTY = theorem `;
  connected ∅
  by rewrite connected_DEF ConnectedEmpty`;;

let CONNECTED_SING = theorem `;
  ∀a. connected {a}

  proof
    intro_TAC ∀a;
    a ∈ topspace euclidean     [] by fol IN_UNIV TOPSPACE_EUCLIDEAN;
    fol - ConnectedSing connected_DEF;
  qed;
`;;

let CONNECTED_UNIONS = theorem `;
  ∀P.  (∀s. s ∈ P ⇒ connected s) ∧ ¬(INTERS P = ∅)
    ⇒ connected(UNIONS P)

  proof
    intro_TAC ∀P;
    ∀s. s ∈ P ⇒ s ⊂ topspace euclidean     [] by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN;
    fol - connected_DEF ConnectedUnions;
  qed;
`;;

let CONNECTED_UNION = theorem `;
  ∀s t.  connected s  ∧  connected t  ∧  ¬(s ∩ t = ∅)
    ⇒ connected (s ∪ t)

  proof
    intro_TAC ∀s t;
    s ⊂ topspace euclidean  ∧  t ⊂ topspace euclidean     [] by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN;
    fol - connected_DEF ConnectedUnion;
  qed;
`;;

let CONNECTED_DIFF_OPEN_FROM_CLOSED = theorem `;
  ∀s t u.  s ⊂ t  ∧  t ⊂ u  ∧  open s  ∧  closed t  ∧
    connected u ∧ connected(t ━ s)
    ⇒  connected(u ━ s)
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN connected_DEF OPEN_IN CLOSED_IN ConnectedDiffOpenFromClosed`;;

(* ------------------------------------------------------------------------- *)
(* Limit points.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("limit_point_of",(12,"right"));;

let limit_point_of_DEF = NewDefinition `;
  x limit_point_of s  ⇔  x ∈ LimitPointOf euclidean s`;;

let limit_point_of = theorem `;
  x limit_point_of s  ⇔
    ∀t. x ∈ t ∧ open t  ⇒  ∃y. ¬(y = x) ∧ y ∈ s ∧ y ∈ t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN IN_UNIV IN_LimitPointOf limit_point_of_DEF OPEN_IN`;;

let LIMPT_SUBSET = theorem `;
  ∀x s t.  x limit_point_of s ∧ s ⊂ t  ⇒  x limit_point_of t
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN limit_point_of_DEF LimptSubset SUBSET`;;

let CLOSED_LIMPT = theorem `;
  ∀s.  closed s  ⇔  ∀x. x limit_point_of s ⇒ x ∈ s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN IN_UNIV limit_point_of_DEF CLOSED_IN ClosedLimpt SUBSET`;;

let LIMPT_EMPTY = theorem `;
  ∀x.  ¬(x limit_point_of ∅)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN IN_UNIV limit_point_of_DEF GSYM ∉ LimptEmpty`;;

let NO_LIMIT_POINT_IMP_CLOSED = theorem `;
  ∀s. ¬(∃x. x limit_point_of s) ⇒ closed s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN IN_UNIV limit_point_of_DEF CLOSED_IN NoLimitPointImpClosed NOT_EXISTS_THM ∉`;;

let LIMIT_POINT_UNION = theorem `;
  ∀s t x.  x limit_point_of (s ∪ t)  ⇔
    x limit_point_of s  ∨  x limit_point_of t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN IN_UNIV limit_point_of_DEF LimitPointUnion EXTENSION IN_UNION`;;

let LimitPointOf_euclidean = theorem `;
  ∀s.  LimitPointOf euclidean s = {x | x limit_point_of s}
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN IN_UNIV limit_point_of_DEF LimitPointOf IN_ELIM_THM EXTENSION`;;

(* ------------------------------------------------------------------------- *)
(* Interior of a set.                                                        *)
(* ------------------------------------------------------------------------- *)

let interior_DEF = NewDefinition `;
  interior = Interior euclidean`;;

let interior = theorem `;
  ∀s. interior s = {x | ∃t. open t ∧ x ∈ t ∧ t ⊂ s}
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF Interior_DEF OPEN_IN`;;

let INTERIOR_EQ = theorem `;
  ∀s.  interior s = s  ⇔  open s

  proof
    simplify interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN InteriorEq;
    fol;
  qed;
`;;

let INTERIOR_OPEN = theorem `;
  ∀s.  open s  ⇒  interior s = s
  by fol interior_DEF OPEN_IN InteriorOpen`;;

let INTERIOR_EMPTY = theorem `;
  interior ∅ = ∅
  by fol interior_DEF OPEN_IN InteriorEmpty`;;

let INTERIOR_UNIV = theorem `;
  interior UNIV = UNIV
  by simplify INTERIOR_OPEN OPEN_UNIV`;;

let OPEN_INTERIOR = theorem `;
  ∀s. open (interior s)
  by simplify interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN  OpenInterior`;;

let INTERIOR_INTERIOR = theorem `;
  ∀s. interior (interior s) = interior s
  by simplify interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN  InteriorInterior`;;

let INTERIOR_SUBSET = theorem `;
  ∀s. interior s ⊂ s
  by simplify interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN  InteriorSubset`;;

let SUBSET_INTERIOR = theorem `;
  ∀s t.  s ⊂ t  ⇒  interior s ⊂ interior t
  by simplify interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN SubsetInterior`;;

let INTERIOR_MAXIMAL = theorem `;
  ∀s t.  t ⊂ s ∧ open t  ⇒  t ⊂ interior s
  by simplify interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN InteriorMaximal`;;

let INTERIOR_MAXIMAL_EQ = theorem `;
  ∀s t.  open s  ⇒  (s ⊂ interior t ⇔ s ⊂ t)
  by simplify interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN InteriorMaximalEq`;;

let INTERIOR_UNIQUE = theorem `;
  ∀s t.  t ⊂ s  ∧  open t ∧  (∀t'. t' ⊂ s ∧ open t' ⇒ t' ⊂ t)
    ⇒ interior s = t
  by simplify interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN InteriorUnique`;;

let IN_INTERIOR = theorem `;
  ∀x s.  x ∈ interior s  ⇔  ∃e. &0 < e ∧ ball(x,e) ⊂ s

  proof
    simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF IN_Interior GSYM OPEN_IN;
    fol OPEN_CONTAINS_BALL SUBSET_TRANS CENTRE_IN_BALL OPEN_BALL;
  qed;
`;;

let OPEN_SUBSET_INTERIOR = theorem `;
  ∀s t.  open s  ⇒  (s ⊂ interior t  ⇔  s ⊂ t)
  by fol interior_DEF OPEN_IN SUBSET_UNIV TOPSPACE_EUCLIDEAN OpenSubsetInterior`;;

let INTERIOR_INTER = theorem `;
  ∀s t. interior (s ∩ t) = interior s ∩ interior t
  by simplify interior_DEF SUBSET_UNIV TOPSPACE_EUCLIDEAN InteriorInter`;;

let INTERIOR_FINITE_INTERS = theorem `;
  ∀s.  FINITE s  ⇒  interior (INTERS s) = INTERS (IMAGE interior s)

  proof
  intro_TAC ∀s, H1;
    case_split sEmpty | sNonempty by fol;
    suppose s = ∅;
      rewrite INTERS_0 IMAGE_CLAUSES sEmpty INTERIOR_UNIV;
    end;
    suppose ¬(s = ∅);
      simplify  SUBSET_UNIV TOPSPACE_EUCLIDEAN H1 sNonempty interior_DEF InteriorFiniteInters;
    end;
  qed;
`;;

let INTERIOR_INTERS_SUBSET = theorem `;
  ∀f.  interior (INTERS f) ⊂ INTERS (IMAGE interior f)

  proof
    intro_TAC ∀f;
    case_split fEmpty | fNonempty by fol;
    suppose f = ∅;
      rewrite INTERS_0 IMAGE_CLAUSES fEmpty INTERIOR_UNIV SUBSET_REFL;
    end;
    suppose ¬(f = ∅);
      fol SUBSET_UNIV TOPSPACE_EUCLIDEAN fNonempty interior_DEF InteriorIntersSubset;
    end;
  qed;
`;;

let UNION_INTERIOR_SUBSET = theorem `;
  ∀s t.  interior s ∪ interior t  ⊂  interior(s ∪ t)
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF UnionInteriorSubset`;;

let INTERIOR_EQ_EMPTY = theorem `;
  ∀s.  interior s = ∅  ⇔  ∀t. open t ∧ t ⊂ s ⇒ t = ∅
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF OPEN_IN InteriorEqEmpty`;;

let INTERIOR_EQ_EMPTY_ALT = theorem `;
  ∀s.  interior s = ∅  ⇔  ∀t. open t ∧ ¬(t = ∅) ⇒ ¬(t ━ s = ∅)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF OPEN_IN InteriorEqEmptyAlt`;;

let INTERIOR_UNIONS_OPEN_SUBSETS = theorem `;
  ∀s.  UNIONS {t | open t ∧ t ⊂ s} = interior s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF OPEN_IN InteriorUnionsOpenSubsets`;;

(* ------------------------------------------------------------------------- *)
(* Closure of a set.                                                         *)
(* ------------------------------------------------------------------------- *)

let closure_DEF = NewDefinition `;
  closure = Closure euclidean`;;

let closure = theorem `;
  ∀s.  closure s = s UNION {x | x limit_point_of s}
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF LimitPointOf_euclidean Closure_THM`;;

let CLOSURE_INTERIOR = theorem `;
  ∀s. closure s = UNIV ━ interior (UNIV ━ s)

  proof
    rewrite closure_DEF GSYM TOPSPACE_EUCLIDEAN interior_DEF;
    simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN ClosureInterior;
  qed;
`;;

let INTERIOR_CLOSURE = theorem `;
  ∀s.  interior s = UNIV ━ (closure (UNIV ━ s))

  proof
    rewrite closure_DEF GSYM TOPSPACE_EUCLIDEAN  interior_DEF;
    simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN InteriorClosure;
  qed;
`;;

let CLOSED_CLOSURE = theorem `;
  ∀s.  closed (closure s)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosedClosure`;;

let CLOSURE_SUBSET = theorem `;
  ∀s.  s ⊂ closure s
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureSubset`;;

let SUBSET_CLOSURE = theorem `;
  ∀s t.  s ⊂ t  ⇒  closure s ⊂ closure t
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF SubsetClosure`;;

let CLOSURE_HULL = theorem `;
  ∀s. closure s = closed hull s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureHull`;;

let CLOSURE_EQ = theorem `;
  ∀s.  closure s = s  ⇔  closed s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureEq`;;

let CLOSURE_CLOSED = theorem `;
  ∀s.  closed s  ⇒  closure s = s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureClosed`;;

let CLOSURE_CLOSURE = theorem `;
  ∀s.  closure (closure s) = closure s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureClosure`;;

let CLOSURE_UNION = theorem `;
  ∀s t.  closure (s ∪ t)  =  closure s ∪ closure t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureUnion`;;

let CLOSURE_INTER_SUBSET = theorem `;
  ∀s t.  closure (s ∩ t)  ⊂  closure s ∩ closure t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureInterSubset`;;

let CLOSURE_INTERS_SUBSET = theorem `;
  ∀f.  closure (INTERS f)  ⊂  INTERS (IMAGE closure f)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureIntersSubset`;;

let CLOSURE_MINIMAL = theorem `;
  ∀s t.  s ⊂ t ∧ closed t  ⇒  closure s ⊂ t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureMinimal`;;

let CLOSURE_MINIMAL_EQ = theorem `;
  ∀s t.  closed t  ⇒  (closure s ⊂ t ⇔ s ⊂ t)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureMinimalEq`;;

let CLOSURE_UNIQUE = theorem `;
  ∀s t.  s ⊂ t ∧ closed t ∧ (∀t'. s ⊂ t' ∧ closed t' ⇒ t ⊂ t')
    ⇒ closure s = t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN closure_DEF ClosureUnique`;;

let CLOSURE_EMPTY = theorem `;
  closure ∅ = ∅
  by fol closure_DEF ClosureEmpty`;;

let CLOSURE_UNIV = theorem `;
  closure UNIV = UNIV
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF CLOSED_IN_TOPSPACE ClosureEq`;;

let CLOSURE_UNIONS = theorem `;
  ∀f.  FINITE f  ⇒  closure (UNIONS f) = UNIONS {closure s | s ∈ f}
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF ClosureUnions`;;

let CLOSURE_EQ_EMPTY = theorem `;
  ∀s.  closure s = ∅  ⇔  s = ∅
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF ClosureEqEmpty`;;

let CLOSURE_SUBSET_EQ = theorem `;
  ∀s.  closure s ⊂ s  ⇔  closed s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF CLOSED_IN ClosureSubsetEq`;;

let OPEN_INTER_CLOSURE_EQ_EMPTY = theorem `;
  ∀s t.  open s  ⇒  (s ∩ closure t = ∅  ⇔  s ∩ t = ∅)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF OPEN_IN OpenInterClosureEqEmpty`;;

let OPEN_INTER_CLOSURE_SUBSET = theorem `;
  ∀s t.  open s  ⇒  s ∩ closure t ⊂ closure (s ∩ t)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF OPEN_IN OpenInterClosureSubset`;;

let CLOSURE_OPEN_INTER_SUPERSET = theorem `;
  ∀s t.  open s ∧ s ⊂ closure t  ⇒  closure (s ∩ t) = closure s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF OPEN_IN ClosureOpenInterSuperset`;;

let CLOSURE_COMPLEMENT = theorem `;
  ∀s.  closure (UNIV ━ s) = UNIV ━ interior s

  proof
    rewrite closure_DEF GSYM TOPSPACE_EUCLIDEAN  interior_DEF;
    simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN ClosureComplement;
  qed;
`;;

let INTERIOR_COMPLEMENT = theorem `;
  ∀s.  interior (UNIV ━ s) = UNIV ━ closure s

  proof
    rewrite closure_DEF GSYM TOPSPACE_EUCLIDEAN  interior_DEF;
    simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN InteriorComplement;
  qed;
`;;

let CONNECTED_INTERMEDIATE_CLOSURE = theorem `;
  ∀s t.  connected s ∧ s ⊂ t ∧ t ⊂ closure s  ⇒  connected t
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF connected_DEF ConnectedIntermediateClosure`;;

let CONNECTED_CLOSURE = theorem `;
  ∀s.  connected s  ⇒  connected (closure s)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF connected_DEF ConnectedClosure`;;

let CONNECTED_UNION_STRONG = theorem `;
  ∀s t.  connected s ∧ connected t ∧ ¬(closure s ∩ t = ∅)
        ⇒ connected (s ∪ t)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF connected_DEF ConnectedUnionStrong`;;

let INTERIOR_DIFF = theorem `;
  ∀s t.  interior (s ━ t) = interior s ━ closure t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF interior_DEF InteriorDiff`;;

let CLOSED_IN_LIMPT = theorem `;
  ∀s t.  closed_in (subtopology euclidean t) s  ⇔
    s ⊂ t  ∧  ∀x. x limit_point_of s ∧ x ∈ t ⇒ x ∈ s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF limit_point_of_DEF ClosedInLimpt_ALT`;;

let CLOSED_IN_INTER_CLOSURE = theorem `;
  ∀s t.  closed_in (subtopology euclidean s) t  ⇔  s ∩ closure t = t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF limit_point_of_DEF ClosedInInterClosure`;;

let INTERIOR_CLOSURE_IDEMP = theorem `;
  ∀s. interior (closure (interior (closure s))) = interior (closure s)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF interior_DEF InteriorClosureIdemp`;;

let CLOSURE_INTERIOR_IDEMP = theorem `;
  ∀s.  closure (interior (closure (interior s))) = closure (interior s)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF interior_DEF ClosureInteriorIdemp`;;

let INTERIOR_CLOSED_UNION_EMPTY_INTERIOR = theorem `;
  ∀s t.  closed s ∧ interior t = ∅  ⇒  interior (s ∪ t) = interior s
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN interior_DEF InteriorClosedUnionEmptyInterior`;;

let INTERIOR_UNION_EQ_EMPTY = theorem `;
  ∀s t.  closed s ∨ closed t
        ⇒ (interior (s ∪ t) = ∅  ⇔  interior s = ∅ ∧ interior t = ∅)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN CLOSED_IN interior_DEF InteriorUnionEqEmpty`;;

let NOWHERE_DENSE_UNION = theorem `;
  ∀s t.  interior (closure (s ∪ t)) = ∅  ⇔
        interior (closure s) = ∅  ∧  interior (closure t) = ∅
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF interior_DEF NowhereDenseUnion`;;

let NOWHERE_DENSE = theorem `;
  ∀s.  interior (closure s) = ∅ ⇔
    ∀t. open t ∧ ¬(t = ∅)  ⇒  ∃u. open u ∧ ¬(u = ∅) ∧ u ⊂ t ∧ u ∩ s = ∅
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF closure_DEF OPEN_IN NowhereDense`;;

let INTERIOR_CLOSURE_INTER_OPEN = theorem `;
  ∀s t.  open s ∧ open t ⇒
    interior (closure (s ∩ t))  =  interior(closure s) ∩ interior (closure t)
  by simplify interior_DEF closure_DEF OPEN_IN InteriorClosureInterOpen`;;

let CLOSURE_INTERIOR_UNION_CLOSED = theorem `;
  ∀s t.  closed s ∧ closed t  ⇒
    closure (interior (s ∪ t))  = closure (interior s) ∪ closure (interior t)
  by simplify interior_DEF closure_DEF CLOSED_IN ClosureInteriorUnionClosed`;;

let REGULAR_OPEN_INTER = theorem `;
  ∀s t.  interior (closure s) = s ∧ interior (closure t) = t
    ⇒ interior (closure (s ∩ t)) = s ∩ t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF closure_DEF RegularOpenInter`;;

let REGULAR_CLOSED_UNION = theorem `;
  ∀s t.  closure (interior s) = s  ∧  closure (interior t) = t
    ⇒  closure (interior (s ∪ t)) = s ∪ t
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN interior_DEF closure_DEF RegularClosedUnion`;;

let DIFF_CLOSURE_SUBSET = theorem `;
  ∀s t.  closure s ━ closure t ⊂ closure (s ━ t)
  by fol SUBSET_UNIV TOPSPACE_EUCLIDEAN closure_DEF DiffClosureSubset`;;

(* ------------------------------------------------------------------------- *)
(* Frontier (aka boundary).                                                  *)
(* ------------------------------------------------------------------------- *)

let frontier_DEF = NewDefinition `;
  frontier = Frontier euclidean`;;

let frontier = theorem `;
  ∀s.  frontier s = (closure s) DIFF (interior s)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN frontier_DEF closure_DEF interior_DEF Frontier_THM`;;

let FRONTIER_CLOSED  = theorem `;
  ∀s. closed (frontier s)
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN frontier_DEF CLOSED_IN FrontierClosed`;;

let FRONTIER_CLOSURES = theorem `;
  ∀s. frontier s = (closure s) INTER (closure (UNIV DIFF s))
  by simplify SUBSET_UNIV TOPSPACE_EUCLIDEAN frontier_DEF closure_DEF FrontierClosures`;;
