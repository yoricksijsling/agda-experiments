
-- Trying to establish relations between contexts. Especially a _startingWith_
-- relation on context variables would be useful.

module DatatypeDescriptions.CxEq where

open import Prelude
open import Shared.Semantics

infixl 0 _▷_ _▷Set _▶_

-- Exactly Σ, but looks better with the nesting produced by Cx.
record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop
open _▶_ public

mutual
  data Cx : Set₂ where
    _▷Set : (Γ : Cx) → Cx
    _▷_ : (Γ : Cx)(S : ⟦ Γ ⟧Cx → Set) → Cx
    ε : Cx

  ⟦_⟧Cx : Cx → Set₁
  ⟦ Γ ▷Set ⟧Cx = (⟦ Γ ⟧Cx ▶ const Set)
  ⟦ Γ ▷ S ⟧Cx = (⟦ Γ ⟧Cx ▶ S)
  ⟦ ε ⟧Cx = ⊤′

instance Cx-semantics : Semantics Cx
         Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }
{-# DISPLAY ⟦_⟧Cx x = ⟦_⟧ x #-}

data StartsWith : (Γ Δ : Cx) → Set where
  instance base : ∀{Γ} → StartsWith Γ Γ
  instance step : ∀{Γ Δ}{{sub : StartsWith Γ Δ}} → {S : ⟦ Γ ⟧Cx → Set} → StartsWith (Γ ▷ S) Δ
  instance stepSet : ∀{Γ Δ}{{sub : StartsWith Γ Δ}} → StartsWith (Γ ▷Set) Δ

data startsWith : {Γ Δ : Cx} (SW : StartsWith Γ Δ) → ⟦ Γ ⟧ → ⟦ Δ ⟧ → Set where
  instance base : ∀{Γ} → (γ : ⟦ Γ ⟧) → startsWith (base {Γ}) γ γ
  instance step : ∀{Γ Δ}{SW : StartsWith Γ Δ}{S : ⟦ Γ ⟧Cx → Set} →
                  {γ : ⟦ Γ ⟧}{δ : ⟦ Δ ⟧}{s : S γ}{{sw : startsWith SW γ δ}} → startsWith (step {{SW}} {S}) (γ , s) δ
  instance stepSet : ∀{Γ Δ}{SW : StartsWith Γ Δ} →
                     {γ : ⟦ Γ ⟧}{δ : ⟦ Δ ⟧}{s : Set}{{sw : startsWith SW γ δ}} → startsWith (stepSet {{SW}}) (γ , s) δ

-- CxOn :
partialCx : {Γ Δ : Cx}(SW : StartsWith Γ Δ) → ⟦ Γ ⟧ → ⟦ Δ ⟧
partialCx base γ = γ
partialCx (step {{SW}}) (γ , s) = partialCx SW γ
partialCx (stepSet {{SW}}) (γ , s) = partialCx SW γ

module _ where
  private
    A : StartsWith ε ε 
    A = it

    B : StartsWith (ε ▷Set) ε
    B = it

    C : StartsWith (ε ▷Set ▷ top) (ε ▷Set ▷ top)
    C = it

    D : StartsWith ((ε ▷ (const Nat)) ▷Set ▷ top) (ε ▷ (const Nat))
    D = it

    a : startsWith A tt tt
    a = it

    b : startsWith B (tt , Nat) tt
    b = it

    c : startsWith C ((tt , Nat) , 10) ((tt , Nat) , 10)
    c = it

    d : startsWith D (((tt , 15) , Nat) , 12) (tt , 15)
    d = it

    fo : (Γ₀ Γ : Cx){{SW : StartsWith Γ Γ₀}} → (γ₀ : ⟦ Γ₀ ⟧) → (γ : ⟦ Γ ⟧) → {{sw : startsWith SW γ γ₀}} → Nat
    fo Γ₀ Γ γ₀ γ = 0

    X : Cx
    X = ε ▷Set ▷ top
    Y : Cx
    Y = ε ▷Set ▷ top ▷ top ∘ pop
    x : ⟦ X ⟧
    x = (tt , Nat) , 15
    y : ⟦ Y ⟧
    y = ((tt , Nat) , 15) , 13

    fa : Nat
    fa = fo X Y x y
