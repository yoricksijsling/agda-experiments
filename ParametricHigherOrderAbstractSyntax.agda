
-- Adam Chlipala - Parametric Higher Order Abstract Syntax for Mechanized Semantics

module ParametricHigherOrderAbstractSyntax where

open import Prelude

----------------------------------------
-- Untyped lambda calculus HOAS

-- Not strictly positive:

-- data Term : Set where
--   App : Term → Term → Term
--   Abs : (Term → Term) → Term


----------------------------------------
-- Untyped lambda calculus PHOAS

module LC where
  data Term′ (A : Set) : Set where
    Var : A → Term′ A
    App : Term′ A → Term′ A → Term′ A
    Abs : (A → Term′ A) → Term′ A

  Term : Set₁
  Term = ∀ A → Term′ A

  numVars : Term′ ⊤ → Nat
  numVars (Var _) = 1
  numVars (App e₁ e₂) = numVars e₁ + numVars e₂
  numVars (Abs e′) = numVars (e′ tt)

  NumVars : Term → Nat
  NumVars E = numVars (E ⊤)

----------------------------------------
-- Simply Typed Lambda Calculus PHOAS

module STLC where
  data Type : Set where
    `bool : Type
    _`→_ : Type → Type → Type
  
  data Term′ (A : Type → Set) : Type → Set where
    Var : ∀{t} → A t → Term′ A t
    Tru : Term′ A `bool
    Fals : Term′ A `bool
    App : ∀{s t} → Term′ A (s `→ t) → Term′ A s → Term′ A t
    Abs : ∀{s t} → (A s → Term′ A t) → Term′ A (s `→ t)

  Term : Type → Set₁
  Term t = ∀ A → Term′ A t

  example : Term `bool
  example A = Tru

  example2 : Term (`bool `→ `bool)
  example2 A = Abs (λ x → Var x)


module STLCSemantics where
  open STLC
  open import Shared.Semantics

  ⟦_⟧ty : Type → Set
  ⟦ `bool ⟧ty = Bool
  ⟦ s `→ t ⟧ty = ⟦ s ⟧ty → ⟦ t ⟧ty
  
  ⟦_⟧tm′ : ∀{t} → Term′ ⟦_⟧ty t → ⟦ t ⟧ty
  ⟦ Var x ⟧tm′ = x
  ⟦ Tru ⟧tm′ = true
  ⟦ Fals ⟧tm′ = false
  ⟦ App e₁ e₂ ⟧tm′ = ⟦ e₁ ⟧tm′ ⟦ e₂ ⟧tm′
  ⟦ Abs e ⟧tm′ = λ x → ⟦ e x ⟧tm′

  instance tm′-semantics : ∀{t} → Semantics (Term′ ⟦_⟧ty t)
           tm′-semantics = record { ⟦_⟧ = ⟦_⟧tm′ }

  ⟦_⟧tm : ∀{t} → Term t → ⟦ t ⟧ty
  ⟦ E ⟧tm = ⟦ E ⟦_⟧ty ⟧

  instance tm-semantics : ∀{t} → Semantics (Term t)
           tm-semantics = record { ⟦_⟧ = ⟦_⟧tm }

  test-example : ⟦ example ⟧ ≡ true
  test-example = refl

  test-example2 : ⟦ example2 ⟧ true ≡ true
  test-example2 = refl
  test-example2′ : ⟦ example2 ⟧ false ≡ false
  test-example2′ = refl
