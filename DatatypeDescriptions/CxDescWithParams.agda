
-- The indices can actually depend on the parameters.
-- It should be possible to implement this but it all becomes quite messy.
-- The easy part is to pass a Cx for the parameters and then let the indices
-- depend on it. It becomes hard when you then want the rest of the Cx within
-- the constructors depend on that, and at the same time you want to keep the
-- parameter-part of the Cx to construct the indices. One of the problems here
-- is that there are places where you first want the values of the parameters
-- to obtain the index type, and after that the rest of the values. There is not
-- an obvious way to pass only 'the rest of the values'.




module DatatypeDescriptions.CxDescWithParams where

open import Prelude
open import Shared.Semantics

Pow : Set → Set₁
Pow I = I → Set

module Context where
  infixl 0 _▷_ _▷Set _▶_

  -- Exactly Σ, but looks better with the nesting produced by Cx.
  record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      pop : A
      top : B pop
  open _▶_ public

  map▶ : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
           (f : A₁ → A₂) → (∀ {x} → B₁ x → B₂ (f x)) → A₁ ▶ B₁ → A₂ ▶ B₂
  map▶ f g (x , y) = f x , g y


  mutual
    data Cx′ (A : Set₁) : Set₂ where
      _▷Set : (Γ : Cx′ A) → Cx′ A
      _▷_ : (Γ : Cx′ A)(S : ⟦ Γ ⟧Cx′ → Set) → Cx′ A
      start : Cx′ A

    ⟦_⟧Cx′ : {A : Set₁} → Cx′ A → Set₁
    ⟦ Γ ▷Set ⟧Cx′ = ⟦ Γ ⟧Cx′ ▶ const Set
    ⟦ Γ ▷ S ⟧Cx′ = ⟦ Γ ⟧Cx′ ▶ S
    ⟦_⟧Cx′ {A = A} start = A

  instance Cx′-semantics : ∀{A} → Semantics (Cx′ A)
           Cx′-semantics = record { ⟦_⟧ = ⟦_⟧Cx′ }
  {-# DISPLAY ⟦_⟧Cx′ x = ⟦_⟧ x #-}

  -- mutual
  --   data Cx (A : Set₁) : Set₂ where
  --     _▷Set : (Γ : Cx A) → Cx A
  --     _▷_ : (Γ : Cx A)(S : (a : A) → ⟦ Γ ⟧Cx a → Set) → Cx A
  --     start : Cx A
  --   ⟦_⟧Cx : {A : Set₁} → Cx A → A → Set₁
  --   ⟦ Γ ▷Set ⟧Cx a = ⟦ Γ ⟧Cx a ▶ const Set
  --   ⟦ Γ ▷ S ⟧Cx a = ⟦ Γ ⟧Cx a ▶ S a
  --   ⟦ start ⟧Cx a = ⊤′

  -- ⟦_⟧CxT : Cx ⊤′ → Set₁
  -- ⟦ Γ ⟧CxT = ⟦ Γ ⟧Cx tt

  -- G : Cx ⊤′
  -- G = start ▷ (λ a x → Nat)
  -- F : Cx ⟦ G ⟧CxT
  -- F = start ▷ (λ a x → {!!})

  envVars : ∀{A} → (Γ : Cx′ A) → ⟦ Γ ⟧ → A
  envVars (Γ ▷Set) (γ , _) = envVars Γ γ
  envVars (Γ ▷ _) (γ , _) = envVars Γ γ
  envVars start γ = γ

  -- Replace Γ's environment of type A with type B
  -- Return the Cx using the new environment, and a function which can be used
  -- the variables in the Cx with the new environment to variables in the old
  -- context.
  mutual
    replaceEnv : ∀{A B} → (f : B → A) → (Γ : Cx′ A) → Cx′ B
    replaceEnv f (Γ ▷Set) = replaceEnv f Γ ▷Set
    replaceEnv f (Γ ▷ S) = replaceEnv f Γ ▷ S ∘ translateReplaceEnv f Γ
    replaceEnv f start = start
    translateReplaceEnv : ∀{A B} → (f : B → A) → (Γ : Cx′ A) → ⟦ replaceEnv f Γ ⟧ → ⟦ Γ ⟧
    translateReplaceEnv f (Γ ▷Set) (δ , s) = translateReplaceEnv f Γ δ , s
    translateReplaceEnv f (Γ ▷ S) (δ , s) = translateReplaceEnv f Γ δ , s
    translateReplaceEnv f start r = f r

  -- Replace the environment with a constant value
  mutual
    setEnv : ∀{A} → (Γ : Cx′ A) → (a : A) → Cx′ ⊤′
    setEnv Γ a = replaceEnv (const a) Γ
    translateSetEnv : ∀{A} → (Γ : Cx′ A) → (a : A) → ⟦ setEnv Γ a ⟧ → ⟦ Γ ⟧
    translateSetEnv Γ a = translateReplaceEnv (const a) Γ

  private
    untransport▶ : ∀ {a b} {A : Set a} {B : A → Set b} {x₁ x₂ : A} {y : B x₂} →
                   (eq : x₁ ≡ x₂) → _≡_ {A = A ▶ B} (x₁ , transport B (sym eq) y) (x₂ , y)
    untransport▶ refl = refl

  mutual
    localVars : ∀{A}(Γ : Cx′ A) → (γ : ⟦ Γ ⟧) → ⟦ setEnv Γ (envVars Γ γ) ⟧
    localVars (Γ ▷Set) (γ , s) = localVars Γ γ , transport (const Set) (sym (localVarsEq Γ γ)) s
    localVars (Γ ▷ S) (γ , s) = localVars Γ γ , transport S (sym (localVarsEq Γ γ)) s
    localVars start γ = tt

    localVarsEq : ∀{A}(Γ : Cx′ A) → (γ : ⟦ Γ ⟧) → translateSetEnv Γ (envVars Γ γ) (localVars Γ γ) ≡ γ
    localVarsEq (Γ ▷Set) (γ , s) = untransport▶ (localVarsEq Γ γ)
    localVarsEq (Γ ▷ S) (γ , s) = untransport▶ (localVarsEq Γ γ)
    localVarsEq start γ = refl

  splitCx : ∀{A}(Γ : Cx′ A) → ⟦ Γ ⟧ → Σ A (⟦_⟧ ∘ setEnv Γ)
  splitCx Γ γ = envVars Γ γ , localVars Γ γ

  postulate
    combineCx : ∀{A}(Γ : Cx′ A) (a : A) → ⟦ setEnv Γ a ⟧ → ⟦ Γ ⟧
  -- combineCx (Γ ▷Set) a (δ , s) = {!!}
  -- combineCx (Γ ▷ S) a (δ , s) = (combineCx Γ a δ) , {!s!}
  -- combineCx start a _ = a

-- (γ₀ : ⟦ Γ₀ ⟧)(γ : ⟦ setEnv Γ γ₀ ⟧)

--   module CxExample where
--     private
--       G : Cx′ ⊤′
--       G = start ▷ (const Nat)
--       F : Cx′ ⟦ G ⟧
--       F = start ▷ Fin ∘ top
--       ex : ⟦ F ⟧
--       ex = (tt , 10) , 5
--       ex1 : ⟦ inst F (tt , 10) ⟧
--       ex1 = tt , 5
--       ex2 : dual-⟦⟧ G F
--       ex2 = (tt , 10) , (tt , 5)


  -- Wrap this function in a record to help the type checker
  -- record Cxf {Γ₀ Δ₀}(Γ : Cx Γ₀)(Δ : Cx Δ₀) : Set₁ where
  record Cxf (Γ Δ : Cx′ ⊤′) : Set₁ where
    constructor mk
    field
      apply : ⟦ Γ ⟧ → ⟦ Δ ⟧
  open Cxf

  cxf-make : ∀ Γ Δ → (⟦ Γ ⟧ → ⟦ Δ ⟧) → Cxf Γ Δ
  cxf-make _ _ = mk
  
  cxf-id : ∀ Γ → Cxf Γ Γ
  cxf-id Γ = mk id

  cxf-∘ : ∀{Γ Δ Χ} → (f : Cxf Δ Χ) → (g : Cxf Γ Δ) → Cxf Γ Χ
  cxf-∘ f g = mk (apply f ∘ apply g)

  cxf-both : ∀{Γ Δ S} → (f : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ apply f)) (Γ ▷ S)
  cxf-both f = mk λ δ → apply f (pop δ) , top δ

  cxf-forget : ∀{Γ Δ} → (f : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
  cxf-forget f S = mk λ δ → apply f (pop δ)

  cxf-instantiate : ∀{Γ Δ S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → S (apply f γ)) → Cxf Δ (Γ ▷ S)
  cxf-instantiate f s = mk λ δ → (apply f δ) , s δ

  cxf-instantiateSet : ∀{Γ Δ} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Δ ⟧) → Set) → Cxf Δ (Γ ▷Set)
  cxf-instantiateSet f s = mk λ δ → (apply f δ) , s δ


-- module Simple where
--   open Context public
  
--   infixr 3 _`+_
--   infixr 4 _`*_
--   data ConDesc : Cx → Set₁ where
--     ι : ∀{Γ} → ConDesc Γ
--     _`*_ : ∀{Γ}(S : ⟦ Γ ⟧ → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
--     rec-`*_ : ∀{Γ}(xs : ConDesc Γ) → ConDesc Γ
--   data DatDesc : Nat → Set₁ where
--     `0 : DatDesc 0
--     _`+_ : ∀{#c}(x : ConDesc ε)(xs : DatDesc #c) → DatDesc (suc #c)

--   lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc ε
--   lookupCtor `0 ()
--   lookupCtor (x `+ _) zero = x
--   lookupCtor (_ `+ xs) (suc k) = lookupCtor xs k

--   ⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧ → Set → Set
--   ⟦ ι ⟧conDesc γ X = ⊤
--   ⟦ S `* xs ⟧conDesc γ X = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X
--   ⟦ rec-`* xs ⟧conDesc γ X = X × ⟦ xs ⟧conDesc γ X
--   -- Note how the context is not passed to the child. An environment _should_ be passed though!
--   ⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
--   ⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc tt X

--   data μ {#c : Nat}(F : DatDesc #c) : Set where
--     ⟨_⟩ : ⟦ F ⟧datDesc (μ F) → μ F

--   ----------------------------------------
--   -- Folding

--   DatAlg : ∀{#c} → DatDesc #c → Set → Set
--   DatAlg D X = ⟦ D ⟧datDesc X → X
--   ConAlg : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧ → Set → Set
--   ConAlg D γ X = ⟦ D ⟧conDesc γ X → X

--   module Fold {#c}{D : DatDesc #c}{X} (α : DatAlg D X) where
--     mutual
--       fold : μ D → X
--       fold ⟨ xs ⟩ = α (datDescmap-fold D xs) -- D and xs are the starting arguments

--       -- Map the fold. It recurses on the description and needs local contexts
--       -- to do the mapping. But when the fold is called all this can be
--       -- forgotten.
--       conDescmap-fold : ∀{Γ′} (D′ : ConDesc Γ′) {γ′} (xs : ⟦ D′ ⟧conDesc γ′ (μ D)) → ⟦ D′ ⟧conDesc γ′ X
--       conDescmap-fold ι tt = tt
--       conDescmap-fold (S `* xs) (s , v) = s , conDescmap-fold xs v
--       conDescmap-fold (rec-`* xs) (s , v) = fold s , conDescmap-fold xs v
--       datDescmap-fold : ∀{#c} (D′ : DatDesc #c) (xs : ⟦ D′ ⟧datDesc (μ D)) → ⟦ D′ ⟧datDesc X
--       datDescmap-fold `0 (() , _)
--       datDescmap-fold (x `+ xs) (k , v) = k , conDescmap-fold (lookupCtor (x `+ xs) k) v
--   open Fold using (fold) public

module IndicesAndParams where
  open Context public
  {-
  Pass the parameters in the context.
   - Parameters can only be accessed in the same places where context can be
     accessed.
   - The way of accessing them is the same as for context. All the DeBruijn
     indices match up with the DeBruijn indices in the quoted datatype.

  So DatDesc receives a context. I _think_ all the updates to the context are
  forgotten in the recursive arguments (because γ is not passed along in the
  semantics of rec). Only the parameters are kept due to the fixpoint.
  -}
  
  ----------------------------------------
  -- Universe

  record ParamsIndices : Set₂ where
    field
      Γ₀ : Cx′ ⊤′
      I₀ : ⟦ Γ₀ ⟧ → Set
    Cx : Set₂
    Cx = Cx′ ⟦ Γ₀ ⟧
    I : (Γ : Cx) → ⟦ Γ ⟧ → Set
    I Γ γ = I₀ (envVars Γ γ)

  module Definition (PI : ParamsIndices) where
    open ParamsIndices PI public

    infixr 3 _`+_
    infixr 4 _`*_
    data ConDesc : (Γ : Cx′ ⟦ Γ₀ ⟧) → Set₁ where
      ι : ∀{Γ} → (o : (γ : ⟦ Γ ⟧) → I Γ γ) → ConDesc Γ
      _`*_ : ∀{Γ} → (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
      rec_`*_ : ∀{Γ} → (i : (γ : ⟦ Γ ⟧) → I Γ γ) → (xs : ConDesc Γ) → ConDesc Γ
    data DatDesc : (#c : Nat) → Set₁ where
      `0 : DatDesc 0
      _`+_ : ∀{#c}(x : ConDesc start)(xs : DatDesc #c) → DatDesc (suc #c)

    lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc start
    lookupCtor `0 ()
    lookupCtor (x `+ _) zero = x
    lookupCtor (_ `+ xs) (suc k) = lookupCtor xs k

    private
      ⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → (γ₀ : ⟦ Γ₀ ⟧)(γ : ⟦ setEnv Γ γ₀ ⟧) → Pow (I₀ γ₀) → Pow (I₀ γ₀)
      ⟦ ι o ⟧conDesc γ₀ γ X o′ = {!combineCx!} ≡ o′
      ⟦ S `* xs ⟧conDesc γ₀ γ X o = {!!}
      ⟦ rec i `* xs ⟧conDesc γ₀ γ X o = {!!}
      -- ⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → (γ₀ : ⟦ Γ₀ ⟧)(γ : ⟦ inst γ₀ Γ ⟧) →  Pow (I₀ γ₀) → Pow (I₀ γ₀)
      -- ⟦_⟧conDesc = {!!}
      -- ⟦ ι o ⟧conDesc γ X o′ = o γ ≡ o′
      -- ⟦ S `* xs ⟧conDesc γ X o = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X o
      -- ⟦ rec i `* xs ⟧conDesc γ X o = X (i γ) × ⟦ xs ⟧conDesc γ X o
    -- ⟦_⟧desc : ∀{#c} → DatDesc #c → (γ₀ : ⟦ Γ₀ ⟧) → Pow (I₀ γ₀) → Pow (I₀ γ₀)
    -- ⟦_⟧desc {#c} D γ₀ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc γ₀ X o

--     private
--       ⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → (γ : ⟦ Γ ⟧) → Pow (I Γ γ) → Pow (I Γ γ)
--       ⟦ ι o ⟧conDesc γ X o′ = o γ ≡ o′
--       ⟦ S `* xs ⟧conDesc γ X o = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X o
--       ⟦ rec i `* xs ⟧conDesc γ X o = X (i γ) × ⟦ xs ⟧conDesc γ X o
--     ⟦_⟧desc : ∀{#c} → DatDesc #c → (γ : ⟦ Γ₀ ⟧) → Pow (I start γ) → Pow (I start γ)
--     ⟦_⟧desc {#c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc γ X o

--     instance conDesc-semantics : ∀{Γ} → Semantics (ConDesc Γ)
--              conDesc-semantics = record { ⟦_⟧ = ⟦_⟧conDesc }
--              desc-semantics : ∀{#c} → Semantics (DatDesc #c)
--              desc-semantics = record { ⟦_⟧ = ⟦_⟧desc }
--     {-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
--     {-# DISPLAY ⟦_⟧desc x = ⟦_⟧ x #-}


--     data μ {#c} (F : DatDesc #c) (γ₀ : ⟦ Γ₀ ⟧) (o : I₀ γ₀) : Set where
--       ⟨_⟩ : ⟦ F ⟧ γ₀ (μ F γ₀) o → μ F γ₀ o


--   ----------------------------------------
--   -- Map

--   module Map (PI : ParamsIndices) where --(γ₀ : ⟦ ParamsIndices.Γ₀ PI ⟧) where
--     open Definition PI

--     private
--       conDescmap : ∀{Γ γ X Y} (f : ∀{i : I Γ γ} → X i → Y i) (D : ConDesc Γ) →
--                    ∀{i} → (xs : ⟦ D ⟧ γ X i) → ⟦ D ⟧ γ Y i
--       conDescmap f (ι o) refl = refl
--       conDescmap f (S `* xs) (s , v) = s , conDescmap f xs v
--       conDescmap f (rec i `* xs) (s , v) = f s , conDescmap f xs v
--     descmap : ∀{γ₀ X Y #c} (f : ∀{i : I₀ γ₀} → X i → Y i) (D : DatDesc #c) →
--               ∀{i} → (xs : ⟦ D ⟧ γ₀ X i) → ⟦ D ⟧ γ₀ Y i
--     descmap f `0 (() , _)
--     descmap f (x `+ xs) (k , v) = k , conDescmap f (lookupCtor (x `+ xs) k) v
  
--   ----------------------------------------
--   -- Folding

--   -- Passing the context makes sense, because an algebra may be specific to a
--   -- particular context. If the algebra is for a whole datatype, the context
--   -- corresponds with the parameters. 
--   -- sumAlg : Alg listD (ε ▶ Nat) (const Nat)
--   -- lengthAlg : ∀{A} → Alg listD (ε ▶ A) (const Nat)

--   module Cata (PI : ParamsIndices) where
--     open Definition PI

--     -- ConAlg
--     Alg : ∀{#c} → DatDesc #c → (γ₀ : ⟦ Γ₀ ⟧) → Pow (I₀ γ₀) → Set
--     Alg D γ₀ X = ∀{i} → ⟦ D ⟧ γ₀ X i → X i

--     module Fold {#c}{D : DatDesc #c}{γ₀ X} (α : Alg D γ₀ X) where
--       mutual
--         fold : ∀{i} → μ D γ₀ i → X i
--         fold ⟨ xs ⟩ = α {!!} -- (descmap-fold D xs)

--         -- The normal descmap specialised to fold. Needed for termination checking
--         conDescmap-fold : ∀{Γ} (D′ : ConDesc Γ) {γ i} (xs : ⟦ D′ ⟧ γ (μ D (base Γ γ)) i) → ⟦ D′ ⟧ γ {!X!} i
--         conDescmap-fold = {!!}
        
--         -- descmap-fold : ∀{dt Γ′} (D′ : Desc I Γ′ dt) {γ′ i} (xs : ⟦ D′ ⟧ γ′ (μ D γ) i) → ⟦ D′ ⟧ γ′ X i
--         -- descmap-fold {`contag} (ι o) refl = refl
--         -- descmap-fold {`contag} (S `* xs) (s , v) = s , descmap-fold xs v
--         -- descmap-fold {`contag} (rec i′ `* xs) (s , v) = fold s , descmap-fold xs v
--         -- descmap-fold {`dattag _} `0 (() , _)
--         -- descmap-fold {`dattag _} (x `+ xs) (k , v) = k , descmap-fold (lookupCtor (x `+ xs) k) v

-- --       conDescmap-fold : ∀{Γ′} (D′ : ConDesc Γ′) {γ′} (xs : ⟦ D′ ⟧conDesc γ′ (μ D)) → ⟦ D′ ⟧conDesc γ′ X
-- --       conDescmap-fold ι tt = tt
-- --       conDescmap-fold (S `* xs) (s , v) = s , conDescmap-fold xs v
-- --       conDescmap-fold (rec-`* xs) (s , v) = fold s , conDescmap-fold xs v
-- --       datDescmap-fold : ∀{#c} (D′ : DatDesc #c) (xs : ⟦ D′ ⟧datDesc (μ D)) → ⟦ D′ ⟧datDesc X
-- --       datDescmap-fold `0 (() , _)
-- --       datDescmap-fold (x `+ xs) (k , v) = k , conDescmap-fold (lookupCtor (x `+ xs) k) v

--     open Fold using (fold) public

-- --   Alg : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → Pow I → Set
-- --   Alg {I} D γ X = {i : I} → ⟦ D ⟧ γ X i → X i

-- --   module Fold {I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) where
-- --     mutual
-- --       fold : {i : I} → μ D γ i → X i
-- --       fold ⟨ xs ⟩ = α (descmap-fold D xs)

-- --       -- The normal descmap specialised to fold. Needed for termination checking
-- --       descmap-fold : ∀{dt Γ′} (D′ : Desc I Γ′ dt) {γ′ i} (xs : ⟦ D′ ⟧ γ′ (μ D γ) i) → ⟦ D′ ⟧ γ′ X i
-- --       descmap-fold {`contag} (ι o) refl = refl
-- --       descmap-fold {`contag} (S `* xs) (s , v) = s , descmap-fold xs v
-- --       descmap-fold {`contag} (rec i′ `* xs) (s , v) = fold s , descmap-fold xs v
-- --       descmap-fold {`dattag _} `0 (() , _)
-- --       descmap-fold {`dattag _} (x `+ xs) (k , v) = k , descmap-fold (lookupCtor (x `+ xs) k) v
-- --   open Fold using (fold) public


-- -- module Examples where
-- --   open IndicesAndParams

-- --   someFinD : DatDesc ⊤ ε 1
-- --   someFinD = const Nat `* const Bool `* (λ γ → Fin (top (pop γ))) `* ι (const tt) `+ `0
-- --   someFinD-ex : μ someFinD tt tt
-- --   someFinD-ex = ⟨ 0 , 10 , true , 3 , refl ⟩

-- --   wrapeqD : DatDesc ⊤ (ε ▷Set) 1
-- --   wrapeqD = top `* top ∘ pop `* (λ γ → (top (pop γ)) ≡ (top γ)) `* ι (const tt) `+ `0
-- --   wrapeqD-mk : ∀{A}(x y : A) → x ≡ y → μ wrapeqD (tt , A) tt
-- --   wrapeqD-mk x y x=y = ⟨ 0 , x , y , x=y , refl ⟩
  
-- --   countFields : ∀{Γ} → ConDesc ⊤ Γ → Nat
-- --   countFields (ι o) = 0
-- --   countFields (S `* xs) = suc (countFields xs)
-- --   countFields (rec i `* xs) = suc (countFields xs)

-- --   vecD : DatDesc Nat (ε ▷Set) 2
-- --   vecD = ι (const 0) `+
-- --          const Nat `* top ∘ pop `* rec (top ∘ pop) `* ι (suc ∘ top ∘ pop) `+
-- --          `0
-- --   vecD-nil : ∀{A} → μ vecD (tt , A) 0
-- --   vecD-nil = ⟨ 0 , refl ⟩
-- --   vecD-cons : ∀{A n} → A → μ vecD (tt , A) n → μ vecD (tt , A) (suc n)
-- --   vecD-cons x xs = ⟨ 1 , _ , x , xs , refl ⟩
