
-- Nils Anders Danielsson
-- A Formalisation of a Dependently Typed Language as Inductive-Recursive Family

module FormalisationOfADepTypedLanguage where

open import Prelude

module Simple where
  mutual
    data Ctxt : Set where
      ε : Ctxt
      _▷_ : (Γ : Ctxt) → Ty Γ → Ctxt

    data Ty : Ctxt → Set where
      ⋆ : ∀{Γ} → Ty Γ
      Π : ∀{Γ} (τ : Ty Γ) → Ty (Γ ▷ τ) → Ty Γ
      El : ∀{Γ} → Γ ⊢ ⋆ → Ty Γ

    data _⊢_ : (Γ : Ctxt) → Ty Γ → Set where
      var : Γ ∋ τ → Γ ⊢ τ
