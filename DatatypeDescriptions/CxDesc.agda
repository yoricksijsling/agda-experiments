
-- Descriptions using contexts
-- Implementation somewhat inspired by Conor McBride's Outrageous but Meaningful Coincidences

module DatatypeDescriptions.CxDesc where

open import Prelude
open import Shared.Semantics

Pow : Set → Set₁
Pow I = I → Set


module Context where
  -- _▶_ is exactly Σ but with nesting suitable for our purposes
  infixl 0 _▶_
  data _▶_  {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    _,_ : (x : A) (y : B x) → A ▶ B

  pop : ∀ {a b} {A : Set a} {B : A → Set b} → A ▶ B → A
  pop (x , y) = x

  top : ∀ {a b} {A : Set a} {B : A → Set b} (p : A ▶ B) → B (pop p)
  top (x , y) = y

  infixl 0 _▷_
  mutual
    data Cx : Set₂ where
      _▷Set : (Γ : Cx) → Cx
      _▷_ : (Γ : Cx)(S : ⟦ Γ ⟧Cx → Set) → Cx
      ε : Cx
    ⟦_⟧Cx : Cx → Set₁
    ⟦ Γ ▷Set ⟧Cx = ⟦ Γ ⟧Cx ▶ const Set
    ⟦ Γ ▷ S ⟧Cx = ⟦ Γ ⟧Cx ▶ S
    ⟦ ε ⟧Cx = ⊤′

  instance Cx-semantics : Semantics Cx
           Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }
  {-# DISPLAY ⟦_⟧Cx x = ⟦_⟧ x #-}
  
  -- infix 3 _∋_
  -- data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧ → Set) → Set₁ where
  --   top : ∀{Γ T} → Γ ▷ T ∋ T ∘ fst
  --   pop : ∀{Γ S T} → Γ ∋ T → Γ ▷ S ∋ T ∘ fst

  -- ⟦_⟧∋ : ∀{Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧) → T γ
  -- ⟦ top ⟧∋ (_ , t) = t
  -- ⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

  -- Wrap this function in a record to help the type checker
  record Cxf (Γ Δ : Cx) : Set₁ where
    constructor mk
    field
      apply : ⟦ Γ ⟧ → ⟦ Δ ⟧
  -- open Cxf

  cxf-ε : Cxf ε ε
  cxf-ε = mk id

  cxf-id : ∀ {Γ} → Cxf Γ Γ
  cxf-id = mk id

  cxf-both : ∀{Γ Δ S} → (f : Cxf Δ Γ) → Cxf (Δ ▷ (S ∘ Cxf.apply f)) (Γ ▷ S)
  cxf-both f = mk λ { (δ , s) → Cxf.apply f δ , s }

  cxf-forget : {Γ Δ : Cx} → (f : Cxf Δ Γ) → (S : ⟦ Δ ⟧ → Set) → Cxf (Δ ▷ S) Γ
  cxf-forget f S = mk λ { (δ , _) → Cxf.apply f δ }

  cxf-instantiate : ∀{Γ Δ S} → (f : Cxf Δ Γ) → (s : (γ : ⟦ Γ ⟧) → S γ) → Cxf Δ (Γ ▷ S)
  cxf-instantiate f s = mk λ {x → (Cxf.apply f x) , s (Cxf.apply f x)}

  -- cxf-both-id : ∀{Γ S} → cxf-both {Γ = Γ} {S = S} (cxf-id {Γ}) ≡ cxf-id {Γ ▷ S}
  -- cxf-both-id {Γ} {S} = cong mk {!Cxf.apply (cxf-id {Γ})!}


module Simple where
  open Context public
  
  infixr 3 _`+_
  infixr 4 _`*_
  data ConDesc : Cx → Set₁ where
    ι : ∀{Γ} → ConDesc Γ
    _`*_ : ∀{Γ}(S : ⟦ Γ ⟧ → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
    rec-`*_ : ∀{Γ}(xs : ConDesc Γ) → ConDesc Γ
  data DatDesc : Nat → Set₁ where
    `0 : DatDesc 0
    _`+_ : ∀{#c}(x : ConDesc ε)(xs : DatDesc #c) → DatDesc (suc #c)

  lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc ε
  lookupCtor `0 ()
  lookupCtor (x `+ _) zero = x
  lookupCtor (_ `+ xs) (suc k) = lookupCtor xs k

  ⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧ → Set → Set
  ⟦ ι ⟧conDesc γ X = ⊤
  ⟦ S `* xs ⟧conDesc γ X = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X
  ⟦ rec-`* xs ⟧conDesc γ X = X × ⟦ xs ⟧conDesc γ X
  -- Note how the context is not passed to the child. An environment _should_ be passed though!
  ⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
  ⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc tt X

  data μ {#c : Nat}(F : DatDesc #c) : Set where
    ⟨_⟩ : ⟦ F ⟧datDesc (μ F) → μ F

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

  infixr 3 _`+_
  infixr 4 _`*_
  data ConDesc (I : Set) : (Γ : Cx) → Set₁ where
    ι : ∀{Γ} → (o : (γ : ⟦ Γ ⟧) → I) → ConDesc I Γ
    _`*_ : ∀{Γ} → (S : (γ : ⟦ Γ ⟧) → Set) → (xs : ConDesc I (Γ ▷ S)) → ConDesc I Γ
    rec_`*_ : ∀{Γ} → (i : (γ : ⟦ Γ ⟧) → I) → (xs : ConDesc I Γ) → ConDesc I Γ
  data DatDesc (I : Set)(Γ : Cx) : (#c : Nat) → Set₁ where
    `0 : DatDesc I Γ 0
    _`+_ : ∀{#c}(x : ConDesc I Γ)(xs : DatDesc I Γ #c) → DatDesc I Γ (suc #c)

  ----------------------------------------
  -- Semantics

  data DescTag : Set₂ where
    `contag : DescTag
    `dattag : (#c : Nat) → DescTag

  Desc : (I : Set) → (Γ : Cx) → DescTag → Set₁
  Desc I Γ (`contag) = ConDesc I Γ
  Desc I Γ (`dattag #c) = DatDesc I Γ #c

  lookupCtor : ∀{I Γ #c}(D : DatDesc I Γ #c) → Fin #c → ConDesc I Γ
  lookupCtor `0 ()
  lookupCtor (x `+ _) zero = x
  lookupCtor (_ `+ xs) (suc k) = lookupCtor xs k

  private
    ⟦_⟧conDesc : ∀{I Γ} → ConDesc I Γ → ⟦ Γ ⟧ → Pow I → Pow I
    ⟦ ι o ⟧conDesc γ X o′ = o γ ≡ o′
    ⟦ S `* xs ⟧conDesc γ X o = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X o
    ⟦ rec i `* xs ⟧conDesc γ X o = X (i γ) × ⟦ xs ⟧conDesc γ X o
  ⟦_⟧desc : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → Pow I → Pow I
  ⟦_⟧desc {dt = `contag} = ⟦_⟧conDesc
  ⟦_⟧desc {dt = `dattag #c} D γ X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc γ X o
  
  instance desc-semantics : ∀{I Γ dt} → Semantics (Desc I Γ dt)
           desc-semantics = record { ⟦_⟧ = ⟦_⟧desc }
  {-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
  {-# DISPLAY ⟦_⟧desc x = ⟦_⟧ x #-}

  data μ {I Γ #c} (F : DatDesc I Γ #c) (γ : ⟦ Γ ⟧) (o : I) : Set where
    ⟨_⟩ : ⟦ F ⟧ γ (μ F γ) o → μ F γ o

  ----------------------------------------
  -- Map

  descmap : ∀{I Γ dt X Y} (f : ∀{i : I} → X i → Y i) (D : Desc I Γ dt) →
            ∀{γ i} → (xs : ⟦ D ⟧ γ X i) → ⟦ D ⟧ γ Y i
  descmap {dt = `contag} f (ι o) refl = refl
  descmap {dt = `contag} f (S `* xs) (s , v) = s , descmap f xs v
  descmap {dt = `contag} f (rec i `* xs) (s , v) = f s , descmap f xs v
  descmap {dt = `dattag _} f `0 (() , _)
  descmap {dt = `dattag _} f (x `+ xs) (k , v) = k , descmap f (lookupCtor (x `+ xs) k) v
  
  ----------------------------------------
  -- Folding

  Alg : ∀{I Γ dt} → Desc I Γ dt → ⟦ Γ ⟧ → Pow I → Set
  Alg {I} D γ X = {i : I} → ⟦ D ⟧ γ X i → X i

  module Fold {I Γ #c}{D : DatDesc I Γ #c}{γ X} (α : Alg D γ X) where
    mutual
      fold : {i : I} → μ D γ i → X i
      fold ⟨ xs ⟩ = α (descmap-fold D xs)

      -- The normal descmap specialised to fold. Needed for termination checking
      descmap-fold : ∀{dt Γ′} (D′ : Desc I Γ′ dt) {γ′ i} (xs : ⟦ D′ ⟧ γ′ (μ D γ) i) → ⟦ D′ ⟧ γ′ X i
      descmap-fold {`contag} (ι o) refl = refl
      descmap-fold {`contag} (S `* xs) (s , v) = s , descmap-fold xs v
      descmap-fold {`contag} (rec i′ `* xs) (s , v) = fold s , descmap-fold xs v
      descmap-fold {`dattag _} `0 (() , _)
      descmap-fold {`dattag _} (x `+ xs) (k , v) = k , descmap-fold (lookupCtor (x `+ xs) k) v
  open Fold using (fold) public


module Examples where
  open IndicesAndParams

  someFinD : DatDesc ⊤ ε 1
  someFinD = const Nat `* const Bool `* (λ γ → Fin (top (pop γ))) `* ι (const tt) `+ `0
  someFinD-ex : μ someFinD tt tt
  someFinD-ex = ⟨ 0 , 10 , true , 3 , refl ⟩

  wrapeqD : DatDesc ⊤ (ε ▷Set) 1
  wrapeqD = top `* top ∘ pop `* (λ γ → (top (pop γ)) ≡ (top γ)) `* ι (const tt) `+ `0
  wrapeqD-mk : ∀{A}(x y : A) → x ≡ y → μ wrapeqD (tt , A) tt
  wrapeqD-mk x y x=y = ⟨ 0 , x , y , x=y , refl ⟩
  
  countFields : ∀{Γ} → ConDesc ⊤ Γ → Nat
  countFields (ι o) = 0
  countFields (S `* xs) = suc (countFields xs)
  countFields (rec i `* xs) = suc (countFields xs)

  vecD : DatDesc Nat (ε ▷Set) 2
  vecD = ι (const 0) `+
         const Nat `* top ∘ pop `* rec (top ∘ pop) `* ι (suc ∘ top ∘ pop) `+
         `0
  vecD-nil : ∀{A} → μ vecD (tt , A) 0
  vecD-nil = ⟨ 0 , refl ⟩
  vecD-cons : ∀{A n} → A → μ vecD (tt , A) n → μ vecD (tt , A) (suc n)
  vecD-cons x xs = ⟨ 1 , _ , x , xs , refl ⟩
