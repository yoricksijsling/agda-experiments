
-- Trying to apply the lessons of 'Adam Chlipala - Parametric Higher Order Abstract Syntax for Mechanized Semantics' to descriptions.

module DescPHOAS where

open import Prelude

module Single where
  mutual
    data Desc : Set where
      `1 : Desc
      `var : Desc
      _`+_ : Desc → Desc → Desc
      `Σ : (C : Desc) → (p : ⟦ C ⟧ ⊤ → Desc) → Desc

    ⟦_⟧ : Desc → Set → Set
    ⟦ `1 ⟧ r = ⊤
    ⟦ `var ⟧ r = r
    ⟦ D `+ D₁ ⟧ r = Either (⟦ D ⟧ r) (⟦ D₁ ⟧ r)
    ⟦ `Σ C p ⟧ r = Σ (⟦ C ⟧ ⊤) (λ x → ⟦ p x ⟧ r)

    data μ (F : Desc) : Set where
      ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

  _`*_ : Desc → Desc → Desc
  D `* D₁ = `Σ D (const D₁)

  fooDesc : Desc
  fooDesc = `Σ (`1 `+ `1) (λ { (left x) → `1
                             ; (right x) → `1 `* `1
                             })

  fooDesc1 : ⟦ fooDesc ⟧ ⊤
  fooDesc1 = left tt , tt
  fooDesc2 : ⟦ fooDesc ⟧ ⊤
  fooDesc2 = right tt , tt , tt

  natDesc : Desc
  natDesc = `var `+ `1

  test-natDesc : μ natDesc
  test-natDesc = ⟨ left ⟨ left ⟨ right tt ⟩ ⟩ ⟩

module ContextFail where
  mutual
    data Desc : Set → Set₁ where
      `1 : ∀ {I} → Desc I
      `var : ∀ {I} → I → Desc I
      _`+_ : ∀ {I} → Desc I → Desc I → Desc I
      `Σ : ∀ {I} → (C : Desc I) → (p : ∀ (cxt : I → Set) (x : Set) → ⟦ C ⟧ cxt x → Desc I) → Desc I

    ⟦_⟧ : ∀ {I} → Desc I → (I → Set) → Set → Set
    ⟦ `1 ⟧ cxt x = ⊤
    ⟦ `var i ⟧ cxt x = cxt i
    ⟦ D `+ D₁ ⟧ cxt x = Either (⟦ D ⟧ cxt x) (⟦ D₁ ⟧ cxt x)
    ⟦ `Σ C p ⟧ cxt x = Σ (⟦ C ⟧ cxt x) (λ v → ⟦ p cxt x v ⟧ cxt x)

-- Not strictly positive!
    -- data μ {I : Set} (cxt : I → Set) (F : Desc I) : Set where
    --   ⟨_⟩ : ⟦ F ⟧ cxt (μ cxt F) → μ cxt F

module Context where
  mutual
    data Desc (A : ∀ {I} → (I → Set) → Set → Set) : Set → Set₁ where
      `1 : ∀ {I} → Desc I
      `var : ∀ {I} → I → Desc I
      _`+_ : ∀ {I} → Desc I → Desc I → Desc I
      -- `Σ : ∀ {I} → (C : Desc ⊥) → (p : (x : Set) → ⟦ C ⟧ ⊥-elim ⊤ → Desc I) → Desc I
      -- `Σ : ∀ {I} → (C : Desc ⊥) → (p : (x : Set) → ⟦ C ⟧ ⊥-elim ⊤ → Desc I) → Desc I

    
  --   ⟦_⟧ : ∀ {I} → Desc I → (I → Set) → Set → Set
  --   ⟦ `1 ⟧ cxt x = ⊤
  --   ⟦ `var i ⟧ cxt x = cxt i
  --   ⟦ D `+ D₁ ⟧ cxt x = Either (⟦ D ⟧ cxt x) (⟦ D₁ ⟧ cxt x)
  --   -- ⟦ `Σ C p ⟧ cxt x = Σ (⟦ C ⟧ cxt x) (λ v → ⟦ p cxt x v ⟧ cxt x)
  --   ⟦ `Σ C p ⟧ cxt x = Σ _ (λ v → ⟦ p x  v ⟧ cxt x)

  --   data μ {I : Set} (cxt : I → Set) (F : Desc I) : Set where
  --     ⟨_⟩ : ⟦ F ⟧ cxt (μ cxt F) → μ cxt F

  -- -- _`*_ : Desc → Desc → Desc
  -- -- D `* D₁ = `Σ D (const D₁)

  -- -- fooDesc : Desc
  -- -- fooDesc = `Σ (`1 `+ `1) (λ { (left x) → `1
  -- --                            ; (right x) → `1 `* `1
  -- --                            })

  -- -- fooDesc1 : ⟦ fooDesc ⟧ ⊤
  -- -- fooDesc1 = left tt , tt
  -- -- fooDesc2 : ⟦ fooDesc ⟧ ⊤
  -- -- fooDesc2 = right tt , tt , tt

  -- -- natDesc : Desc
  -- -- natDesc = `var `+ `1

  -- -- test-natDesc : μ natDesc
  -- -- test-natDesc = ⟨ left ⟨ left ⟨ right tt ⟩ ⟩ ⟩
