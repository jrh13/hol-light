(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* Definitions of FunctionSpace and FunctionComposition.   A proof that the  *)
(* Cartesian product satisfies the universal property that given functions   *)
(* α ∈ M → A and β ∈ M → B, there is a unique γ ∈ M → A ∏ B whose            *)
(* projections to A and B are f and g.                                       *)

needs "RichterHilbertAxiomGeometry/readable.ml";;

ParseAsInfix("∉",(11, "right"));;
ParseAsInfix("∏",(20, "right"));;
ParseAsInfix("∘",(20, "right"));;
ParseAsInfix("→",(13,"right"));;

(*
∉ |- ∀a l. a ∉ l ⇔ ¬(a ∈ l)

CartesianProduct
  |- ∀X Y. X ∏ Y = {x,y | x ∈ X ∧ y ∈ Y}

FUNCTION |- ∀α. FUNCTION α ⇔
             (∃f s t.  α = t,f,s ∧
                  (∀x. x ∈ s ⇒ f x ∈ t) ∧ (∀x. x ∉ s ⇒ f x = (@y. T)))

SOURCE |- ∀α. SOURCE α = SND (SND α)

FUN |- ∀α. FUN α = FST (SND α)

TARGET |- ∀α. TARGET α = FST α

FunctionSpace
  |- ∀s t.  s → t = {α | FUNCTION α ∧ s = SOURCE α ∧ t = TARGET α}

makeFunction
  |- ∀t f s. makeFunction t f s = t,(λx. if x ∈ s then f x else @y. T),s

Projection1Function
  |- ∀X Y. Pi1 X Y = makeFunction X FST (X ∏ Y)

Projection2Function
  |- ∀X Y. Pi2 X Y = makeFunction Y SND (X ∏ Y)

FunctionComposition
  |- ∀α β.  α ∘ β = makeFunction (TARGET α) (FUN α o FUN β) (SOURCE β)

IN_CartesianProduct
  |- ∀X Y x y. x,y ∈ X ∏ Y ⇔ x ∈ X ∧ y ∈ Y

CartesianFstSnd
  |- ∀pair. pair ∈ X ∏ Y ⇒ FST pair ∈ X ∧ SND pair ∈ Y

FUNCTION_EQ
  |- ∀α β.  FUNCTION α ∧ FUNCTION β ∧ SOURCE α = SOURCE β ∧ FUN α = FUN β ∧
        TARGET α = TARGET β  ⇒  α = β

IN_FunctionSpace
  |- ∀s t α.  α ∈ s → t ⇔
         FUNCTION α ∧ s = SOURCE α ∧ t = TARGET α

makeFunction_EQ
  |- ∀f g s t.  (∀x. x ∈ s ⇒ f x = g x)
         ⇒ makeFunction t f s = makeFunction t g s

makeFunctionyieldsFUN
  |- ∀α g t f s.  α = makeFunction t f s ∧ g = FUN α
         ⇒ ∀x. x ∈ s ⇒ f x = g x

makeFunctionEq
  |- ∀α β f g s t.
         α = makeFunction t f s ∧ β = makeFunction t g s ∧
         (∀x. x ∈ s ⇒ f x = g x)  ⇒  α = β

FunctionSpaceOnSource
  |- ∀α f s t.  α ∈ s → t ∧ f = FUN α  ⇒  (∀x. x ∈ s ⇒ f x ∈ t)

FunctionSpaceOnOffSource
  |- ∀α f s t.  α ∈ s → t ∧ f = FUN α
         ⇒ (∀x. x ∈ s ⇒ f x ∈ t) ∧ (∀x. x ∉ s ⇒ f x = (@y. T))

ImpliesTruncatedFunctionSpace
  |- ∀α s t f.
         α = makeFunction t f s ∧ (∀x. x ∈ s ⇒ f x ∈ t)
         ⇒ α ∈ s → t

FunFunctionSpaceImplyFunction
  |- ∀α s t f.  α ∈ s → t ∧ f = FUN α  ⇒  α = makeFunction t f s

UseFunctionComposition
  |- ∀α β u f t g s.
         α = makeFunction u f t ∧ β = makeFunction t g s ∧ β ∈ s → t
         ⇒ α ∘ β = makeFunction u (f o g) s

PairProjectionFunctions
  |- ∀X Y. Pi1 X Y ∈ X ∏ Y → X ∧ Pi2 X Y ∈ X ∏ Y → Y

UniversalPropertyProduct
  |- ∀M A B α β.  α ∈ M → A ∧ β ∈ M → B
                    ⇒ (∃!γ. γ ∈ M → A ∏ B ∧
                       Pi1 A B ∘ γ = α ∧ Pi2 A B ∘ γ = β)

*)

let NOTIN = NewDefinition `;
  ∀a l. a ∉ l ⇔ ¬(a ∈ l)`;;

let CartesianProduct = NewDefinition `;
  ∀X Y. X ∏ Y = {x,y | x ∈ X ∧ y ∈ Y}`;;

let FUNCTION = NewDefinition `;
  FUNCTION α  ⇔  ∃f s t. α = (t, f, s)  ∧
    (∀x. x IN s ⇒ f x  IN t) ∧ ∀x. x ∉ s ⇒ f x  = @y. T`;;

let SOURCE = NewDefinition `;
  SOURCE α = SND (SND α)`;;

let FUN = NewDefinition `;
  FUN α = FST (SND α)`;;

let TARGET = NewDefinition `;
  TARGET α = FST α`;;

let FunctionSpace = NewDefinition `;
  ∀s t. s → t = {α | FUNCTION α  ∧  s = SOURCE α  ∧ t = TARGET α}`;;

let makeFunction = NewDefinition `;
  ∀t f s. makeFunction t f s = (t, (λx. if x ∈ s then f x else @y. T), s)`;;

let Projection1Function = NewDefinition `;
  Pi1 X Y = makeFunction X FST (X ∏ Y)`;;

let Projection2Function = NewDefinition `;
  Pi2 X Y = makeFunction Y SND (X ∏ Y)`;;

let FunctionComposition = NewDefinition `;
  ∀α β.  α ∘ β = makeFunction (TARGET α) (FUN α o FUN β) (SOURCE β)`;;

let IN_CartesianProduct = theorem `;
  ∀X Y x y. x,y ∈ X ∏ Y  ⇔  x ∈ X ∧ y ∈ Y

  proof
    rewrite IN_ELIM_THM CartesianProduct;     fol PAIR_EQ;     qed;
`;;

let IN_CartesianProduct = theorem `;
  ∀X Y x y. x,y ∈ X ∏ Y  ⇔  x ∈ X ∧ y ∈ Y

  proof
    rewrite IN_ELIM_THM CartesianProduct;     fol PAIR_EQ;     qed;
`;;

let CartesianFstSnd = theorem `;
  ∀pair. pair ∈ X ∏ Y  ⇒  FST pair ∈ X ∧ SND pair ∈ Y
  by rewrite FORALL_PAIR_THM PAIR_EQ IN_CartesianProduct`;;

let FUNCTION_EQ = theorem `;
  ∀α β. FUNCTION α  ∧  FUNCTION β  ∧  SOURCE α = SOURCE β  ∧
    FUN α = FUN β  ∧  TARGET α = TARGET β
    ⇒ α = β
  by simplify FORALL_PAIR_THM FUNCTION SOURCE TARGET FUN PAIR FST SND`;;

let IN_FunctionSpace = theorem `;
  ∀s t α. α ∈ s → t
    ⇔  FUNCTION α  ∧  s = SOURCE α  ∧  t = TARGET α
  by rewrite IN_ELIM_THM FunctionSpace`;;

let makeFunction_EQ = theorem `;
  ∀f g s t.  (∀x. x ∈ s ⇒ f x = g x)
    ⇒  makeFunction t f s = makeFunction t g s
  by simplify makeFunction ∉ FUN_EQ_THM`;;

let makeFunctionyieldsFUN = theorem `;
  ∀α g t f s.  α = makeFunction t f s ∧ g = FUN α
    ⇒ ∀x. x ∈ s ⇒ f x = g x
  by simplify makeFunction FORALL_PAIR_THM FUN PAIR_EQ`;;

let makeFunctionEq = theorem `;
  ∀α β f g s t.  α = makeFunction t f s  ∧ β = makeFunction t g s  ∧
    (∀x. x ∈ s ⇒ f x = g x)  ⇒  α = β
  by simplify FORALL_PAIR_THM makeFunction PAIR_EQ`;;

let FunctionSpaceOnSource = theorem `;
  ∀α f s t.  α ∈ s → t  ∧  f = FUN α
    ⇒  ∀x. x ∈ s ⇒ f x ∈ t

  proof
    rewrite FORALL_PAIR_THM IN_FunctionSpace FUNCTION SOURCE TARGET PAIR_EQ FUN FST SND;
    fol;     qed;
`;;

let FunctionSpaceOnOffSource = theorem `;
  ∀α f s t.  α ∈ s → t  ∧  f = FUN α
    ⇒  (∀x. x ∈ s ⇒ f x ∈ t) ∧ ∀x. x ∉ s ⇒ f x = @y. T

  proof
    rewrite FORALL_PAIR_THM IN_FunctionSpace FUNCTION SOURCE TARGET PAIR_EQ FUN FST SND;
    fol;     qed;
`;;

let ImpliesTruncatedFunctionSpace = theorem `;
  ∀α s t f.  α = makeFunction t f s  ∧  (∀x. x ∈ s ⇒ f x ∈ t)
    ⇒ α ∈ s → t

  proof
    rewrite FORALL_PAIR_THM IN_FunctionSpace makeFunction FUNCTION SOURCE TARGET NOTIN PAIR_EQ FST SND;
    fol;     qed;
`;;

let FunFunctionSpaceImplyFunction = theorem `;
  ∀α s t f.  α ∈ s → t  ∧  f = FUN α  ⇒  α = makeFunction t f s

  proof
    rewrite FORALL_PAIR_THM IN_FunctionSpace makeFunction FUNCTION SOURCE TARGET FUN NOTIN PAIR_EQ FST SND;
    fol FUN_EQ_THM;
  qed;
`;;

let UseFunctionComposition = theorem `;
  ∀α β u f t g s. α = makeFunction u f t  ∧
    β = makeFunction t g s  ∧  β ∈ s → t
    ⇒ α _o_ β = makeFunction u (f o g) s

  proof
    rewrite FORALL_PAIR_THM makeFunction FunctionComposition SOURCE TARGET FUN BETA_THM o_THM IN_FunctionSpace FUNCTION SOURCE TARGET NOTIN PAIR_EQ;
    X_genl_TAC u' f' t' t1 g1 s1 u f t g s;
    intro_TAC Hα Hβ Hβ_st Hs Ht;
    (∀x. x ∈ s ⇒ g x ∈ t)     [g_st] by fol Hβ_st Hβ;
    simplify Hα GSYM Hs Hβ g_st;
  qed;
`;;

let PairProjectionFunctions = theorem `;
  ∀X Y. Pi1 X Y ∈ X ∏ Y → X  ∧  Pi2 X Y ∈ X ∏ Y → Y

  proof
    intro_TAC ∀X Y;
    ∀pair. pair ∈ X ∏ Y  ⇒  FST pair ∈ X  ∧ SND pair ∈ Y     [] by fol CartesianFstSnd;
    fol Projection1Function Projection2Function - ImpliesTruncatedFunctionSpace;
  qed;
`;;

let UniversalPropertyProduct = theorem `;
  ∀M A B α β.  α ∈ M → A  ∧  β ∈ M → B
      ⇒  ∃!γ.  γ ∈ M → A ∏ B  ∧  Pi1 A B ∘ γ = α  ∧  Pi2 A B ∘ γ = β

  proof
    intro_TAC ∀M A B α β, H1;
    consider f g such that f = FUN α ∧ g = FUN β     [fgExist] by fol;
    consider h such that h = λx. (f x,g x)     [hExists] by fol;
    ∀x. x ∈ M  ⇒  h x ∈ A ∏ B     [hProd] by fol hExists IN_CartesianProduct H1 fgExist FunctionSpaceOnSource;
    consider γ such that γ = makeFunction (A ∏ B) h  M     [γExists] by fol;
    γ ∈ M → A ∏ B     [γFunSpace] by fol - hProd ImpliesTruncatedFunctionSpace;
    ∀x. x ∈ M  ⇒  (FST o h) x = f x  ∧  (SND o h) x = g x     [h_fg] by simplify hExists FST SND PAIR_EQ o_THM;
    Pi1 A B ∘ γ = makeFunction A (FST o h) M  ∧
    Pi2 A B ∘ γ = makeFunction B (SND o h) M     [] by fol Projection1Function Projection2Function γExists  γFunSpace UseFunctionComposition;
    Pi1 A B ∘ γ = α  ∧  Pi2 A B ∘ γ = β     [γWorks] by fol - h_fg makeFunction_EQ H1 fgExist FunFunctionSpaceImplyFunction;
   ∀θ.  θ ∈ M → A ∏ B  ∧  Pi1 A B ∘ θ = α  ∧  Pi2 A B ∘ θ = β  ⇒ θ = γ     []
     proof
      intro_TAC ∀θ, θWorks;
      consider k such that k = FUN θ     [kExists] by fol;
      θ = makeFunction (A ∏ B) k M     [θFUNk] by fol θWorks - FunFunctionSpaceImplyFunction;
      α = makeFunction A (FST o k) M  ∧  β = makeFunction B (SND o k) M     [] by fol Projection1Function Projection2Function θFUNk θWorks UseFunctionComposition;
      ∀x. x ∈ M  ⇒  f x = (FST o k) x ∧ g x = (SND o k) x     [fg_k] by fol ISPECL [α; f; A; (FST o k); M] makeFunctionyieldsFUN ISPECL [β; g; B; (SND o k); M] makeFunctionyieldsFUN - fgExist;
      ∀x. x ∈ M ⇒ k x = ((FST o k) x, (SND o k) x)     [] by fol PAIR o_THM;
      ∀x. x ∈ M ⇒ k x = (f x, g x)     [] by fol - fg_k PAIR_EQ;
      fol hExists θFUNk γExists  - makeFunctionEq;
     qed;
     fol γFunSpace γWorks - EXISTS_UNIQUE_THM;
  qed;
`;;
