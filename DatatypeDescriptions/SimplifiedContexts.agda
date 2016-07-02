
-- A simpler version of contexts, which is suitable if we allow --type-in-type

module DatatypeDescriptions.SimplifiedContexts where

open import Prelude hiding (Applicative′; _<*>′_)
open import Shared.Semantics

infixl 0 _▶_
record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop
open _▶_ public

infixl 0 _▷_
mutual
  data Cx : Set₂ where
    _▷_ : (Γ : Cx)(S : (γ : ⟦ Γ ⟧Cx) → Set) → Cx
    ε : Cx

  ⟦_⟧Cx : Cx → Set₁
  ⟦ Γ ▷ S ⟧Cx = ⟦ Γ ⟧Cx ▶ S
  ⟦ ε ⟧Cx = ⊤′

instance Cx-semantics : Semantics Cx
         Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }

-- S combinator, is also <*> of applicative functor
infixl 4 _<S>_
_<S>_ : ∀ {a b c} {Γ : Set a} {S : Γ → Set b} {T : (γ : Γ) → S γ → Set c} →
  (f : (γ : Γ) (s : S γ) → T γ s) → (s : (γ : Γ) → S γ) →
  (γ : Γ) → T γ (s γ)
_<S>_ = λ f s γ → f γ (s γ)

-- S combined with K gives <$>
infixl 4 _<KS>_
_<KS>_ : ∀ {a b c} {Γ : Set a} {S : Set b} {T : S → Set c} →
  (f : (s : S) → T s) → (s : (γ : Γ) → S) →
  (γ : Γ) → T (s γ)
f <KS> s = const f <S> s

infixr 1 _<,>_
_<,>_ : ∀ {a b c} → {Γ : Set c}{A : Set a}{B : A → Set b} →
        (f : (γ : Γ) → A) → (g : (γ : Γ) → B (f γ)) →
        (γ : Γ) → A ▶ B
(f <,> g) γ = f γ , g γ
