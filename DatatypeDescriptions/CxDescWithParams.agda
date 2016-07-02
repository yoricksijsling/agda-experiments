
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
  open import DatatypeDescriptions.CxEq public

  -- Wrap this function in a record to help the type checker
  -- record Cxf {Γ₀ Δ₀}(Γ : Cx Γ₀)(Δ : Cx Δ₀) : Set₁ where
  record Cxf (Γ Δ : Cx) : Set₁ where
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
  
  record ParamsIndices : Set₂ where
    field
      Γ₀ : Cx
      I₀ : ⟦ Γ₀ ⟧ → Set
    _HasParams : Cx → Set
    Γ HasParams = StartsWith Γ Γ₀

    I : {Γ : Cx} (SW : Γ HasParams) → ⟦ Γ ⟧ → Set
    I SW γ = I₀ (partialCx SW γ)

  module Definition (PI : ParamsIndices) where
    open ParamsIndices PI public

    infixr 3 _`+_
    infixr 4 _`*_
    data ConDesc : (Γ : Cx){{SW : Γ HasParams}} → Set₁ where
      ι : ∀{Γ}{{SW : Γ HasParams}} → (o : (γ : ⟦ Γ ⟧) → I SW γ) → ConDesc Γ
      _`*_ : ∀{Γ}{{SW : Γ HasParams}} → (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
      rec_`*_ : ∀{Γ}{{SW : Γ HasParams}} → (i : (γ : ⟦ Γ ⟧) → I SW γ) → (xs : ConDesc Γ) → ConDesc Γ
    data DatDesc : (#c : Nat) → Set₁ where
      `0 : DatDesc 0
      _`+_ : ∀{#c}(x : ConDesc Γ₀)(xs : DatDesc #c) → DatDesc (suc #c)

    ----------------------------------------
    -- DescTags

    data DescTag : Set₂ where
      `contag : (Γ : Cx){{SW : Γ HasParams}} → DescTag
      `dattag : (#c : Nat) → DescTag

    Desc : DescTag → Set₁
    Desc (`contag Γ) = ConDesc Γ
    Desc (`dattag #c) = DatDesc #c

    Γdt : DescTag → Cx
    Γdt (`contag Γ) = Γ
    Γdt (`dattag #c) = Γ₀

    Γdt-HasParams : (dt : DescTag) → (Γdt dt) HasParams
    Γdt-HasParams (`contag Γ {{SW}}) = SW
    Γdt-HasParams (`dattag #c) = base

    Idt : (dt : DescTag) → ⟦ Γdt dt ⟧ → Set
    Idt dt γ = I (Γdt-HasParams dt) γ

    γdt : (dt : DescTag) → ⟦ Γdt dt ⟧ → ⟦ Γ₀ ⟧
    γdt dt γ = partialCx (Γdt-HasParams dt) γ


    ----------------------------------------
    -- Semantics
    
    lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc Γ₀
    lookupCtor `0 ()
    lookupCtor (x `+ _) zero = x
    lookupCtor (_ `+ xs) (suc k) = lookupCtor xs k

    private
      ⟦_⟧conDesc : ∀{Γ}{{SW : Γ HasParams}} → ConDesc Γ → (γ : ⟦ Γ ⟧) → Pow (I SW γ) → Pow (I SW γ)
      ⟦ ι o ⟧conDesc γ X o′ = o γ ≡ o′
      ⟦ S `* xs ⟧conDesc γ X o = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X o
      ⟦ rec i `* xs ⟧conDesc γ X o = X (i γ) × ⟦ xs ⟧conDesc γ X o
    ⟦_⟧desc : ∀{dt} → Desc dt → (γ : ⟦ Γdt dt ⟧) → Pow (Idt dt γ) → Pow (Idt dt γ)
    ⟦_⟧desc {`contag Γ} = ⟦_⟧conDesc
    ⟦_⟧desc {`dattag #c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc γ X o

    instance desc-semantics : ∀{dt} → Semantics (Desc dt)
             desc-semantics = record { ⟦_⟧ = ⟦_⟧desc }
    {-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
    {-# DISPLAY ⟦_⟧desc x = ⟦_⟧ x #-}

    data μ {#c} (F : DatDesc #c) (γ₀ : ⟦ Γ₀ ⟧) (o : I₀ γ₀) : Set where
      ⟨_⟩ : ⟦ F ⟧ γ₀ (μ F γ₀) o → μ F γ₀ o


  -- ----------------------------------------
  -- -- Map

  -- module Map (PI : ParamsIndices) where --(γ₀ : ⟦ ParamsIndices.Γ₀ PI ⟧) where
  --   open Definition PI public

    -- descmap : ∀{I Γ dt X Y} (f : ∀{i : I} → X i → Y i) (D : Desc I Γ dt) →
    --           ∀{γ i} → (xs : ⟦ D ⟧ γ X i) → ⟦ D ⟧ γ Y i
    -- descmap : ∀{dt γ}{X Y : Idt dt γ → Set} (f : ∀{i : Idt dt γ} → X i → Y i) (D : Desc dt) →
    --           ∀{i} → ⟦ D ⟧ γ X i → ⟦ D ⟧ γ Y i
    -- descmap {`contag Γ} f (ι o) refl = refl
    -- descmap {`contag Γ} f (S `* xs) (s , v) = s , descmap f xs v
    -- descmap {`contag Γ} f (rec i `* xs) (s , v) = f s , descmap f xs v
    -- descmap {`dattag _} f `0 (() , _)
    -- descmap {`dattag _} f (x `+ xs) (k , v) = k , descmap f (lookupCtor (x `+ xs) k) v
    descmap : ∀{dt γ₀}{X Y : I₀ γ₀ → Set} (f : ∀{i} → X i → Y i) (D : Desc dt) →
              ∀{γ i}{sw : startsWith (Γdt-HasParams dt) γ γ₀} → ⟦ D ⟧ γ (X ∘ {!!}) {!!} → {!!} -- ⟦ D ⟧ γ X i → ⟦ D ⟧ γ Y i
    descmap = {!!}
  
-- --   ----------------------------------------
-- --   -- Folding

-- --   -- Passing the context makes sense, because an algebra may be specific to a
-- --   -- particular context. If the algebra is for a whole datatype, the context
-- --   -- corresponds with the parameters. 
-- --   -- sumAlg : Alg listD (ε ▶ Nat) (const Nat)
-- --   -- lengthAlg : ∀{A} → Alg listD (ε ▶ A) (const Nat)

-- --   module Cata (PI : ParamsIndices) where
-- --     open Definition PI

--     -- ConAlg
--     Alg : ∀{#c} → DatDesc #c → (γ₀ : ⟦ Γ₀ ⟧) → Pow (I₀ γ₀) → Set
--     Alg D γ₀ X = ∀{i} → ⟦ D ⟧ γ₀ X i → X i

--     module Fold {#c}{D : DatDesc #c}{γ₀ X} (α : Alg D γ₀ X) where
--       mutual
--         fold : ∀{i} → μ D γ₀ i → X i
--         fold ⟨ xs ⟩ = α {!!} -- (descmap-fold D xs)

-- --         -- The normal descmap specialised to fold. Needed for termination checking
-- --         conDescmap-fold : ∀{Γ} (D′ : ConDesc Γ) {γ i} (xs : ⟦ D′ ⟧ γ (μ D (base Γ γ)) i) → ⟦ D′ ⟧ γ {!X!} i
-- --         conDescmap-fold = {!!}
        
--         descmap-fold : ∀{dt} (D′ : Desc dt) {γ′ i} {{γdt-hasParams → ⟦ D ⟧ (partialCx {!Γdt-HasParams dt!} γ′) (μ D γ₀) {!!} → {!!}
--         -- ⟦ D′ ⟧ γ′ (μ D γ₀) i → ⟦ D′ ⟧ γ′ X i
--         descmap-fold = {!!}
--         -- descmap-fold {`contag} (ι o) refl = refl
--         -- descmap-fold {`contag} (S `* xs) (s , v) = s , descmap-fold xs v
--         -- descmap-fold {`contag} (rec i′ `* xs) (s , v) = fold s , descmap-fold xs v
--         -- descmap-fold {`dattag _} `0 (() , _)
--         -- descmap-fold {`dattag _} (x `+ xs) (k , v) = k , descmap-fold (lookupCtor (x `+ xs) k) v

-- -- --       conDescmap-fold : ∀{Γ′} (D′ : ConDesc Γ′) {γ′} (xs : ⟦ D′ ⟧conDesc γ′ (μ D)) → ⟦ D′ ⟧conDesc γ′ X
-- -- --       conDescmap-fold ι tt = tt
-- -- --       conDescmap-fold (S `* xs) (s , v) = s , conDescmap-fold xs v
-- -- --       conDescmap-fold (rec-`* xs) (s , v) = fold s , conDescmap-fold xs v
-- -- --       datDescmap-fold : ∀{#c} (D′ : DatDesc #c) (xs : ⟦ D′ ⟧datDesc (μ D)) → ⟦ D′ ⟧datDesc X
-- -- --       datDescmap-fold `0 (() , _)
-- -- --       datDescmap-fold (x `+ xs) (k , v) = k , conDescmap-fold (lookupCtor (x `+ xs) k) v

-- --     open Fold using (fold) public

-- -- --   Alg : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → Pow I → Set
-- -- --   Alg {I} D γ X = {i : I} → ⟦ D ⟧ γ X i → X i

-- -- --   module Fold {I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) where
-- -- --     mutual
-- -- --       fold : {i : I} → μ D γ i → X i
-- -- --       fold ⟨ xs ⟩ = α (descmap-fold D xs)

-- -- --       -- The normal descmap specialised to fold. Needed for termination checking
-- -- --       descmap-fold : ∀{dt Γ′} (D′ : Desc I Γ′ dt) {γ′ i} (xs : ⟦ D′ ⟧ γ′ (μ D γ) i) → ⟦ D′ ⟧ γ′ X i
-- -- --       descmap-fold {`contag} (ι o) refl = refl
-- -- --       descmap-fold {`contag} (S `* xs) (s , v) = s , descmap-fold xs v
-- -- --       descmap-fold {`contag} (rec i′ `* xs) (s , v) = fold s , descmap-fold xs v
-- -- --       descmap-fold {`dattag _} `0 (() , _)
-- -- --       descmap-fold {`dattag _} (x `+ xs) (k , v) = k , descmap-fold (lookupCtor (x `+ xs) k) v
-- -- --   open Fold using (fold) public


-- -- -- module Examples where
-- -- --   open IndicesAndParams

-- -- --   someFinD : DatDesc ⊤ ε 1
-- -- --   someFinD = const Nat `* const Bool `* (λ γ → Fin (top (pop γ))) `* ι (const tt) `+ `0
-- -- --   someFinD-ex : μ someFinD tt tt
-- -- --   someFinD-ex = ⟨ 0 , 10 , true , 3 , refl ⟩

-- -- --   wrapeqD : DatDesc ⊤ (ε ▷Set) 1
-- -- --   wrapeqD = top `* top ∘ pop `* (λ γ → (top (pop γ)) ≡ (top γ)) `* ι (const tt) `+ `0
-- -- --   wrapeqD-mk : ∀{A}(x y : A) → x ≡ y → μ wrapeqD (tt , A) tt
-- -- --   wrapeqD-mk x y x=y = ⟨ 0 , x , y , x=y , refl ⟩
  
-- -- --   countFields : ∀{Γ} → ConDesc ⊤ Γ → Nat
-- -- --   countFields (ι o) = 0
-- -- --   countFields (S `* xs) = suc (countFields xs)
-- -- --   countFields (rec i `* xs) = suc (countFields xs)

-- -- --   vecD : DatDesc Nat (ε ▷Set) 2
-- -- --   vecD = ι (const 0) `+
-- -- --          const Nat `* top ∘ pop `* rec (top ∘ pop) `* ι (suc ∘ top ∘ pop) `+
-- -- --          `0
-- -- --   vecD-nil : ∀{A} → μ vecD (tt , A) 0
-- -- --   vecD-nil = ⟨ 0 , refl ⟩
-- -- --   vecD-cons : ∀{A n} → A → μ vecD (tt , A) n → μ vecD (tt , A) (suc n)
-- -- --   vecD-cons x xs = ⟨ 1 , _ , x , xs , refl ⟩
