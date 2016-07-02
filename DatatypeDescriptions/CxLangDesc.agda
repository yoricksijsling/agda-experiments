
{-# OPTIONS --no-positivity-check #-}

-- Descriptions waarbij een kleine geinternaliseerde taal wordt
-- gebruikt om constructorargumenten te representeren.

-- In tegenstelling to LangDesc, voegen we hier geen pi en rec
-- toe. Dus geen extra features tov Cx.Simple.Desc van mn thesis. Het
-- is bedoelt om simpele parameterverwijzingen zoals 'λ γ → pop γ' te
-- kunnen herkennen.

module DatatypeDescriptions.CxLangDesc where

open import Prelude
open import Shared.Semantics

infixl 0 _▷_
mutual
  data Cx : Set₂ where
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx
    -- _▷₁_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set₁) → Cx
    ε : Cx

  ⟦_⟧Cx : Cx → Set₁
  ⟦ Γ ▷ S ⟧Cx = Σ ⟦ Γ ⟧Cx S
  -- ⟦ Γ ▷₁ S ⟧Cx = Σ ⟦ Γ ⟧Cx S
  ⟦ ε ⟧Cx = ⊤′

instance Cx-semantics : Semantics Cx
         Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }

-- data Type : (Γ : Cx) → (⟦ Γ ⟧ → Set) → Set₁ where
--   `lit : (f : ⟦ Γ ⟧ → Set) → Type Γ f
data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧ → Set) → Set₁ where
  top : ∀{Γ T} → (Γ ▷ T) ∋ (T ∘ fst)
  pop : ∀{Γ S T} → Γ ∋ T → (Γ ▷ S) ∋ (T ∘ fst)

⟦_⟧∋ : ∀{Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧) → T γ
⟦ top ⟧∋ (γ , t) = t
⟦ pop i ⟧∋ (γ , s) = ⟦ i ⟧∋ γ

data Type (Γ : Cx) : (⟦ Γ ⟧ → Set) → Set₁ where
  `lit : (f : ⟦ Γ ⟧ → Set) → Type Γ f
  `var : ∀{T} → Γ ∋ T → Type Γ T

-- Dingen met RecType werken alleen zonder positivity-check
data RecType (Γ : Cx) : ((X : Set) → (γ : ⟦ Γ ⟧) → Set) → Set₁ where
  `rec : RecType Γ const
  `Π : ∀{S T} → Type Γ S → RecType (Γ ▷ S) T →
       RecType Γ (λ X γ → (s : S γ) → curry (T X) γ s)


infixr 3 _⊕_
-- infixr 4 _⊗_ rec-⊗_
infixr 4 _⊗_ rec_⊗_
data ConDesc : Cx → Set₁ where
  ι : ∀{Γ} → ConDesc Γ
  _⊗_ : ∀{Γ S}(p : Type Γ S) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
  -- rec-⊗_ : ∀{Γ}(xs : ConDesc Γ) → ConDesc Γ
  rec_⊗_ : ∀{Γ S}(p : RecType Γ S) → (xs : ConDesc Γ) → ConDesc Γ
data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c} (x : ConDesc ε) (xs : DatDesc #c) → DatDesc (suc #c)

lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc ε
lookupCtor `0 ()
lookupCtor (x ⊕ _) zero = x
lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧Cx → Set → Set
⟦ ι ⟧conDesc γ X = ⊤
⟦ _⊗_ {S = S} p xs ⟧conDesc γ X = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X
-- ⟦ rec-⊗ xs ⟧conDesc γ X = X × ⟦ xs ⟧conDesc γ X
⟦ rec_⊗_ {S = S} p xs ⟧conDesc γ X = S X γ × ⟦ xs ⟧conDesc γ X
⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc tt X

instance conDesc-Semantics : ∀{Γ} → Semantics (ConDesc Γ)
         conDesc-Semantics = record { ⟦_⟧ = ⟦_⟧conDesc }
         datDesc-Semantics : ∀{#c} → Semantics (DatDesc #c)
         datDesc-Semantics = record { ⟦_⟧ = ⟦_⟧datDesc }

data μ {#c : Nat}(F : DatDesc #c) : Set where
  ⟨_⟩ : ⟦ F ⟧datDesc (μ F) → μ F

Σ-desc : (A : Set)(B : A → Set) → DatDesc 1
Σ-desc A B = `lit (λ γ → A) ⊗ `lit (B ∘ snd) ⊗ ι ⊕ `0
to-Σ : ∀{A B} → Σ A B → μ (Σ-desc A B)
to-Σ (x , y) = ⟨ 0 , x , y , tt ⟩

-- foo-desc : DatDesc 1
-- foo-desc = `Π (`lit (const Nat)) (`lit (Fin ∘ snd)) ⊗ ι ⊕ `0
-- to-foo : ((n : Nat) → Fin n) → μ foo-desc
-- to-foo f = ⟨ 0 , f , tt ⟩

-- foo : (n : Nat) → ((m : Nat) → n ≡ m → Foo) → n → Foo
foo-desc : DatDesc 1
foo-desc = `lit (const Nat) ⊗ rec `Π (`lit (const Nat)) (`Π (`lit (λ γ → _≡_ (snd γ) (snd (fst γ)))) `rec) ⊗ (`var top ⊗ ι) ⊕ `0


data ListTree (A : Set) : Set where
  node : List (ListTree A) → ListTree A
-- Zelfs met een goede encoding van `rec in Type is ListTree nog
-- steeds niet mogelijk, want de aanroep naar `List` kan niet op een
-- veilige (positive) manier worden gecodeerd. Omdat je niet weet wat
-- List doet, weet je niet of er een negatieve `rec in voorkomt.

-- data Foo : Set where
--   foo : (f : Nat → Foo) → Foo

-- toFoo : Foo → μ fooDesc
-- toFoo (foo f) = ⟨ 0 , (λ x → toFoo (f x)) , tt ⟩
-- fromFoo : μ fooDesc → Foo
-- fromFoo ⟨ zero , f , tt ⟩ = foo (λ x → fromFoo (f x))
-- fromFoo ⟨ suc () , _ ⟩

