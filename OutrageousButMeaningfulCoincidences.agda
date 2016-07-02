
-- Conor McBride - Outrageous but Meaningful coincidences
-- Dependent type-safe syntax and evaluation

module OutrageousButMeaningfulCoincidences where

open import Prelude

module Kipling where
  mutual
    data U : Set where
      `Zero `1 `2 `ℕ : U
      `Π `Σ : (S : U) → (T : El S → U) → U
    El : U → Set
    El `Zero = ⊥
    El `1 = ⊤
    El `2 = Bool
    El `ℕ = Nat
    El (`Π S T) = (s : El S) → El (T s)
    El (`Σ S T) = Σ (El S) λ s → El (T s)
    
  `If : Bool → U → U → U
  `If false t f = t
  `If true t f = f

  _`→_ : U → U → U
  S `→ T = `Π S λ _ → T
  _`×_ : U → U → U
  S `× T = `Σ S λ _ → T

  `Vec : U → Nat → U
  `Vec X zero = `1
  `Vec X (suc n) = X `× `Vec X n


module KiplingContext where
  open Kipling

  mutual
    infixl 4 _▷_
    data Cx : Set where
      ε : Cx
      _▷_ : (Γ : Cx) → (⟦ Γ ⟧Cx → U) → Cx
    ⟦_⟧Cx : Cx → Set
    ⟦ ε ⟧Cx = ⊤
    ⟦ Γ ▷ S ⟧Cx = Σ ⟦ Γ ⟧Cx λ γ → El (S γ)

  someVec : Cx -- (n : Nat) , Vec Bool n , Bool
  someVec = ε ▷ (λ { tt → `ℕ })
              ▷ (λ { (tt , n) → `Vec `2 n })
              ▷ (λ { ((tt , n) , xs) → `2 })

  data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧Cx → U) → Set where
    top : ∀{Γ T} → (Γ ▷ T) ∋ (T ∘ fst)
    pop : ∀{Γ S T} → Γ ∋ T → (Γ ▷ S) ∋ (T ∘ fst)

  ⟦_⟧∋ : ∀{Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧Cx) → El (T γ)
  ⟦ top ⟧∋ (γ , t) = t
  ⟦ pop i ⟧∋ (γ , s) = ⟦ i ⟧∋ γ

  mutual
    -- types with contexts
    data _⋆_ (Γ : Cx) : (⟦ Γ ⟧Cx → U) → Set where
      ``Zero : Γ ⋆ const `Zero
      ``1 : Γ ⋆ const `1
      ``2 : Γ ⋆ const `2
      ``ℕ : Γ ⋆ const `ℕ
      ``Π : ∀{S T} → Γ ⋆ S → (Γ ▷ S) ⋆ T →
            Γ ⋆ (λ γ → `Π (S γ) (λ γs → T (γ , γs)))
      ``Σ : ∀{S T} → Γ ⋆ S → (Γ ▷ S) ⋆ T →
            Γ ⋆ (λ γ → `Σ (S γ) (λ γs → T (γ , γs)))
      ``If : ∀{T F} → (b : Γ ⊢ const `2) →
            Γ ⋆ T → Γ ⋆ F → Γ ⋆ (λ γ → `If (⟦ b ⟧⊢ γ) (T γ) (F γ))

    -- terms with contexts
    data _⊢_ (Γ : Cx) : (⟦ Γ ⟧Cx → U) → Set where
       var : ∀{T} → Γ ∋ T → Γ ⊢ T
       tt : Γ ⊢ const `1
       true false : Γ ⊢ const `2
       zero : Γ ⊢ const `ℕ
       suc : Γ ⊢ const `ℕ → Γ ⊢ const `ℕ
       -- eliminators:
       magic : ∀{T} → Γ ⊢ const `Zero → Γ ⋆ T → Γ ⊢ T
       if : ∀{P} → (b : Γ ⊢ const `2) →
            (Γ ▷ const `2) ⋆ P →
            Γ ⊢ (λ γ → P (γ , true)) → Γ ⊢ (λ γ → P (γ , false)) →
            Γ ⊢ (λ γ → P (γ , (⟦ b ⟧⊢ γ)))
       -- essentially: (b : Bool) → (P : Set) →
       
       -- more terms like abstraction and application can be defined

    ⟦_⟧⊢ : ∀{Γ T} → Γ ⊢ T → (γ : ⟦ Γ ⟧Cx) → El (T γ)
    ⟦ var x ⟧⊢ γ = ⟦ x ⟧∋ γ
    ⟦ tt ⟧⊢ γ = tt
    ⟦ true ⟧⊢ γ = true
    ⟦ false ⟧⊢ γ = false
    ⟦ zero ⟧⊢ γ = zero
    ⟦ suc t ⟧⊢ γ = suc (⟦ t ⟧⊢ γ)
    ⟦ magic z _ ⟧⊢ γ = ⊥-elim (⟦ z ⟧⊢ γ)
    ⟦ if b _ t f ⟧⊢ γ with ⟦ b ⟧⊢ γ
    ⟦ if b _ t f ⟧⊢ γ | true = ⟦ t ⟧⊢ γ
    ⟦ if b _ t f ⟧⊢ γ | false = ⟦ f ⟧⊢ γ
    
    `IsTrue : ∀{Γ} → (b : Γ ⊢ const `2) → Γ ⋆ (λ γ → `If (⟦ b ⟧⊢ γ) `1 `Zero)
    `IsTrue {Γ} b = ``If b ``1 ``Zero
