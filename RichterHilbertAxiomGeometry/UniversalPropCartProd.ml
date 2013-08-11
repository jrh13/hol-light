(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* Definitions of FunctionSpace and FunctionComposition.   A proof that the  *)
(* Cartesian product satisfies the universal property that given functions   *)
(* f ∈ M → A and g ∈ M → B, there is a unique h ∈ M → A ∏ B whose            *)
(* projections to A and B are f and g.                                       *)

needs "RichterHilbertAxiomGeometry/readable.ml";;

(*
parse_as_infix("∉",(11, "right"));;
parse_as_infix("∏",(20, "right"));;
parse_as_infix("∘",(20, "right"));;
parse_as_infix("→",(13,"right"));;

∉     |- ∀a l. a ∉ l ⇔ ¬(a ∈ l)

CartesianProduct
  |- ∀ X Y. X ∏ Y = {x,y | x ∈ X ∧ y ∈ Y}

IN_CartesianProduct
  |- ∀ X Y x y. x,y ∈ X ∏ Y ⇔ x ∈ X ∧ y ∈ Y

FunctionSpace
  |- ∀ s t.     s → t =
         {f | (∀x. x ∈ s ⇒ f x ∈ t) ∧ ∀ x. x ∉ s ⇒ f x = @y. T}

IN_FunctionSpace
  |- ∀ s t f.     f ∈ s → t ⇔
         (∀x. x ∈ s ⇒ f x ∈ t) ∧ ∀x. x ∉ s ⇒ f x = @y. T

FunctionComposition
  |- ∀ f s g x. (g ∘ (f,s)) x = if x ∈ s then g (f x) else @y. T

UniversalPropertyProduct
  |- ∀ M A B f g.
         f ∈ M → A ∧ g ∈ M → B
         ⇒ (∃! h. h ∈ M → A ∏ B  ∧  FST ∘ (h,M) = f  ∧  SND ∘ (h,M) = g)
*)

ParseAsInfix("∉",(11, "right"));;
ParseAsInfix("∏",(20, "right"));;
ParseAsInfix("∘",(20, "right"));;
ParseAsInfix("→",(13,"right"));;

let NOTIN = NewDefinition
  `;∀a l. a ∉ l ⇔ ¬(a ∈ l)`;;

let CartesianProduct = NewDefinition
   `;∀ X Y. X ∏ Y = {x,y | x ∈ X ∧ y ∈ Y}`;;

let FunctionSpace = NewDefinition
  `;∀ s t. s → t = {f | (∀x. x IN s ⇒ f x  IN t) ∧ 
                          ∀x. x ∉ s ⇒ f x  = @y. T}`;;

let FunctionComposition = NewDefinition
  `;∀ f:A->B s:A->bool g:B->C x.
  (g ∘ (f,s)) x = if x ∈ s then g (f x) else @y:C. T`;;

let IN_CartesianProduct = theorem `;
  ∀ X Y x y. x,y ∈ X ∏ Y  ⇔  x ∈ X ∧ y ∈ Y

  proof
    REWRITE_TAC IN_ELIM_THM CartesianProduct;
    fol PAIR_EQ;
  qed;
`;;

let IN_FunctionSpace = theorem `;
  ∀ s t f. f ∈ s → t
    ⇔  (∀ x. x ∈ s ⇒ f x ∈ t)  ∧  ∀ x. x ∉ s ⇒ f x  = @y. T

  proof     REWRITE_TAC IN_ELIM_THM FunctionSpace;     qed;
`;;

let UniversalPropertyProduct = theorem `;
  ∀ M A B f g.
    f ∈ M → A ∧ g ∈ M → B
    ⇒ ∃! h. h ∈ M → A ∏ B  ∧  FST ∘ (h,M) = f  ∧  SND ∘ (h,M) = g

  proof
    intro_TAC ∀ M A B f g, H1;
    (∀ x. x ∈ M ⇒ f x ∈ A)  ∧  ∀x. x ∉ M ⇒ f x = @y. T     [fProp] 
    proof
      mp_TAC_specl [M; A; f] IN_FunctionSpace;     fol H1;     qed;
    (∀ x. x ∈ M ⇒ g x ∈ B)  ∧  (∀x. x ∉ M ⇒ g x = @y. T)     [gProp] 
    proof
      mp_TAC_specl [M; B; g] IN_FunctionSpace;     fol H1;     qed;
    consider h such that
    h = λx. if x ∈ M then f x,g x else @y. T     [hExists] by fol;
    ∀ x. (x ∈ M  ⇒  h x = f x,g x) ∧ (x ∉ M  ⇒  h x = @y. T)     [hDef] by fol - ∉;
    ∀ x. x ∈ M  ⇒  h x ∈ A ∏ B     [hProd] by SIMP_TAC - IN_CartesianProduct fProp gProp;
    ∀ x. x ∈ M  ⇒  (FST ∘ (h,M)) x = f x  ∧  (SND ∘ (h,M)) x = g x     [] 
    proof
      SIMP_TAC hDef FST_DEF SND_DEF PAIR_EQ FunctionComposition;     
      fol PAIR_EQ;
    qed;
    ∀ x. (x ∈ M  ⇒  (FST ∘ (h,M)) x = f x) ∧ (x ∉ M  ⇒  (FST ∘ (h,M)) x = f x)  ∧
    (x ∈ M  ⇒  (SND ∘ (h,M)) x = g x) ∧ (x ∉ M  ⇒  (SND ∘ (h,M)) x = g x)     [] by SIMP_TAC FunctionComposition - IN_FunctionSpace ∉ fProp gProp;
    h ∈ M → A ∏ B  ∧  FST ∘ (h,M) = f  ∧  SND ∘ (h,M) = g     [hWorks] 
    proof     SIMP_TAC hDef hProd IN_FunctionSpace;     fol - ∉ FUN_EQ_THM;     qed;
    ∀ k. (k ∈ M → A ∏ B  ∧  FST ∘ (k,M) = f  ∧  SND ∘ (k,M) = g)  ⇒ h = k     []
    proof
      intro_TAC ∀ k, kWorks;
      (∀ x. x ∈ M ⇒ k x ∈ A ∏ B)  ∧  ∀ x. x ∉ M  ⇒  k x = @y. T     [kOffM] 
      proof     mp_TAC_specl [M; A ∏ B; k] IN_FunctionSpace;     fol kWorks;     qed;
      ∀ x. x ∈ M  ⇒  k x = (FST ∘ (k,M)) x,(SND ∘ (k,M)) x    [] by SIMP_TAC - PAIR FunctionComposition;
      ∀ x. x ∈ M ⇒ k x = f x,g x     [] by SIMP_TAC - kWorks FST_DEF SND_DEF PAIR_EQ;
      SIMP_TAC FUN_EQ_THM;
      fol hDef - kOffM ∉;
    qed;
    fol hWorks - EXISTS_UNIQUE_THM;
  qed;
`;;

