
{-# OPTIONS --type-in-type #-}

-- Internalising contexts, types, terms
-- Based on type theory should it itself

module TermInternalisation where

open import Prelude
open import Shared.Semantics

data Cx : Set
data Ty : (Γ : Cx) → Set
data Tm : ∀ Γ → Ty Γ → Set

data Cx where
  ε : Cx
  _▷_ : ∀ Γ → Ty Γ → Cx

data Ty where
  lit : ∀{Γ} → {!!} → Ty Γ

data Tm where
  
