module SKI where

open import Prelude
open import Shared.Semantics

data Type : Set where
  u : Type
  _⇀_ : Type → Type → Type

infixr 30 _⇀_
⟦_⟧Type : Type → Set
⟦ u ⟧Type = ⊤
⟦ σ ⇀ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

instance Type-semantics : Semantics Type
         Type-semantics = record { ⟦_⟧ = ⟦_⟧Type }

data Comb : Type → Set where
  _⟨_⟩ : ∀ {σ τ} → Comb (σ ⇀ τ) → Comb σ → Comb τ
  S    : ∀ {a b c} → Comb ((a ⇀ b ⇀ c) ⇀ (a ⇀ b) ⇀ a ⇀ c)
  K    : ∀ {a b}  → Comb (a ⇀ b ⇀ a)
  I    : ∀ {a} → Comb (a ⇀ a)

⟦_⟧Comb : ∀{τ} → Comb τ → ⟦ τ ⟧
⟦ x ⟨ y ⟩ ⟧Comb = ⟦ x ⟧Comb ⟦ y ⟧Comb
⟦ S ⟧Comb x y z = x z (y z)
⟦ K ⟧Comb x y = x
⟦ I ⟧Comb x = x

instance Comb-semantics : ∀{τ} → Semantics (Comb τ)
         Comb-semantics = record { ⟦_⟧ = ⟦_⟧Comb }

CombEq : ∀{τ} → Comb τ → Comb τ → Set
CombEq A B = ⟦ A ⟧ ≡ ⟦ B ⟧

Ix=x : ∀{τ} x → (⟦ I {τ} ⟧Comb x) ≡ x
Ix=x x = refl

SKK=I : ∀{a b} → CombEq (S ⟨ K ⟩ ⟨ K {a} {b} ⟩) I
SKK=I = refl
