
{-# OPTIONS --no-positivity-check #-}

-- Descriptions waarbij een kleine geinternaliseerde taal wordt
-- gebruikt om constructorargumenten te representeren.

-- Door de interpretatie naar een pattern functor kunnen we ook
-- recursieve argumenten encoden. Hierbij wordt afgedwongen dat `rec`
-- alleen in strict-positive posities voorkomt.

module DatatypeDescriptions.CxPFLangDesc where

open import Prelude
open import Shared.Semantics

-- Whether Cx should allow functors ((X : Set) → (γ : ⟦ Γ ⟧Cx X) →
-- Set) depends on whether recursive stuff should be stored in the
-- environment. If we want all arguments to be handled by _⊗_ using a
-- Type datatype which supports recs, we can not store some arguments
-- in the context and others not.
infixl 0 _▷_
mutual
  data Cx : Set₂ where
    _▷_ : (Γ : Cx)(S : (X : Set) → (γ : ⟦ Γ ⟧Cx X) → Set) → Cx
    -- _▷₁_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set₁) → Cx
    ε : Cx

  ⟦_⟧Cx : Cx → Set → Set₁
  ⟦ Γ ▷ S ⟧Cx X = Σ (⟦ Γ ⟧Cx X) (S X)
  -- ⟦ Γ ▷₁ S ⟧Cx = Σ ⟦ Γ ⟧Cx S
  ⟦ ε ⟧Cx X = ⊤′

instance Cx-semantics : Semantics Cx
         Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }

-- O : Cx → Set₁ → Set₁
-- O Γ R = (X : Set) → (γ : ⟦ Γ ⟧ X) → R
O : Cx → Set₁
O Γ = (X : Set) → (γ : ⟦ Γ ⟧ X) → Set

data _∋_ : (Γ : Cx) (T : O Γ) → Set₁ where
  top : ∀{Γ T} → (Γ ▷ T) ∋ (λ X → T X ∘ fst)
  pop : ∀{Γ S T} → Γ ∋ T → (Γ ▷ S) ∋ (λ X → T X ∘ fst)

⟦_⟧∋ : ∀{Γ T} → Γ ∋ T → (X : Set) → (γ : ⟦ Γ ⟧ X) → T X γ
⟦ top ⟧∋ X (γ , t) = t
⟦ pop i ⟧∋ X (γ , s) = ⟦ i ⟧∋ X γ

--------------------

data RecAllowed : Set where
  recOk : RecAllowed
  noRec : RecAllowed

data RecType (Γ : Cx) : RecAllowed → O Γ → Set₁ where
  -- lit should never allow rec, because we can not guarantee
  -- strict-positivity
  -- `lit : (f : (γ : ⟦ Γ ⟧ ⊤) → Set) → RecType Γ recOk (λ X → {!!})
  -- `lit : ∀{ra} (f : (γ : ⟦ Γ ⟧ ⊤) → Set) → RecType Γ ra (λ X γ → f {!γ!})
  `Π : ∀{ra S T} → RecType Γ noRec S → RecType (Γ ▷ S) ra T →
       RecType Γ ra (λ X γ → (s : S X γ) → curry (T X) γ s)
  `rec : RecType Γ recOk (λ X γ → X)
  `var : ∀{ra T} → Γ ∋ T → RecType Γ ra T

infixr 3 _⊕_
infixr 4 _⊗_ rec-⊗_
data ConDesc : Cx → Set₁ where
  ι : ∀{Γ} → ConDesc Γ
  _⊗_ : ∀{Γ S}(p : RecType Γ recOk S) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
  rec-⊗_ : ∀{Γ}(xs : ConDesc Γ) → ConDesc Γ
data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c} (x : ConDesc ε) (xs : DatDesc #c) → DatDesc (suc #c)

lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc ε
lookupCtor `0 ()
lookupCtor (x ⊕ _) zero = x
lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → O Γ
⟦ ι ⟧conDesc X γ = ⊤
⟦ _⊗_ {S = S} P xs ⟧conDesc X γ = Σ (S X γ) λ s → ⟦ xs ⟧conDesc X (γ , s)
⟦ rec-⊗ xs ⟧conDesc X γ = X × ⟦ xs ⟧conDesc X γ
⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc X tt

instance conDesc-Semantics : ∀{Γ} → Semantics (ConDesc Γ)
         conDesc-Semantics = record { ⟦_⟧ = ⟦_⟧conDesc }
         datDesc-Semantics : ∀{#c} → Semantics (DatDesc #c)
         datDesc-Semantics = record { ⟦_⟧ = ⟦_⟧datDesc }

data μ {#c : Nat}(F : DatDesc #c) : Set where
  ⟨_⟩ : ⟦ F ⟧datDesc (μ F) → μ F


-- (f : Foo) → (f → Foo) → 
foo-desc : DatDesc 1
foo-desc = `rec ⊗ `Π (`var top) `rec ⊗ {!!} ⊗ ι ⊕ `0
