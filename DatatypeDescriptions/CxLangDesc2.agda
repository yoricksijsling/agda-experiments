
-- Descriptions waarbij een kleine geinternaliseerde taal wordt
-- gebruikt om constructorargumenten te representeren.

-- Variant of LangDesc, nu met contexts

module DatatypeDescriptions.CxLangDesc2 where

open import Prelude
open import Shared.Semantics

infixl 0 _▶_
record _▶_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pop : A
    top : B pop
open _▶_

--------------------
-- Language of terms
-- with contexts

data Cx : Set₁
⟦_⟧Cx : Cx → Set
data Term : (Γ : Cx) → Set₁
⟦_⟧term : ∀{Γ} → Term Γ → ⟦ Γ ⟧Cx → Set

infixl 0 _▷_
data Cx where
  _▷_ : (Γ : Cx)(S : Term Γ) → Cx
  ε : Cx
⟦ Γ ▷ S ⟧Cx = ⟦ Γ ⟧Cx ▶ ⟦ S ⟧term
⟦ ε ⟧Cx = ⊤′

data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧ → Term Γ
-- data " : (Γ : Cx) (T : !Γ"
-- C → U) → Set where
-- top : ∀ {Γ T } → Γ, T"T ·fst
-- pop : ∀ {Γ S T } → Γ"T → Γ, S "T ·fst

data Term where
  arg : ∀{Γ} → ((γ : ⟦ Γ ⟧Cx) → Set) → Term Γ
  topt : ∀{Γ S} → Term (Γ ▷ S)
  -- popt : ∀{Γ S} → Term (Γ ▷ S)
⟦ arg S ⟧term = S
⟦ topt ⟧term (pop , top) = {!!}
-- ⟦ popt ⟧term (pop , top) = {!pop!}



-- with ability for recursion, strictly positive

-- instance Cx-semantics : Semantics Cx
--          Cx-semantics = record { ⟦_⟧ = ⟦_⟧Cx }

-- cxmap : ∀{X Y} → (f : X → Y) → (Γ : Cx) →
--          ⟦ Γ ⟧ X → ⟦ Γ ⟧ Y
-- cxmap f (Γ ▷ S) (γ , s) = cxmap f Γ γ , sptermmap f S s
-- cxmap f ε tt = tt

-- --------------------


-- infixr 3 _⊕_
-- infixr 4 _⊗_
  
-- data ConDesc : Cx → Set₁ where
--   ι : ∀{Γ} → ConDesc Γ
--   _⊗_ : (S : SPTerm recOk) → (xs : ConDesc (Γ ▷ S)) → ConDesc

-- data DatDesc : Nat → Set₁ where
--   `0 : DatDesc 0
--   _⊕_ : ∀{#c} (x : ConDesc) (xs : DatDesc #c) → DatDesc (suc #c)

-- -- ⟦_⟧conDesc : ConDesc → Set → Set
-- -- ⟦ ι ⟧conDesc X = ⊤
-- -- ⟦ S ⊗ D ⟧conDesc X = ⟦ S ⟧spterm X × ⟦ D ⟧conDesc X

-- -- lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc
-- -- lookupCtor `0 ()
-- -- lookupCtor (x ⊕ _) zero = x
-- -- lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

-- -- ⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
-- -- ⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc X

-- -- data μ {#c : Nat}(F : DatDesc #c) : Set where
-- --   ⟨_⟩ : ⟦ F ⟧datDesc (μ F) → μ F


-- -- --------------------
-- -- -- ListTree

-- -- data ListTree (A : Set) : Set where
-- --   node : List (ListTree A) → ListTree A

-- -- -- Nog steeds niet mogelijk, want de aanroep naar `List` wordt niet
-- -- -- gecodeerd in SPTerm. In arbitraire expressies met arg mogen geen
-- -- -- recursieve aanroepen.

-- -- data Foo : Set where
-- --   foo : (f : Nat → Foo) → Foo

-- -- fooDesc : DatDesc 1
-- -- fooDesc = (pi (arg Nat) rec ⊗ ι) ⊕ `0

-- -- toFoo : Foo → μ fooDesc
-- -- toFoo (foo f) = ⟨ 0 , (λ x → toFoo (f x)) , tt ⟩
-- -- fromFoo : μ fooDesc → Foo
-- -- fromFoo ⟨ zero , f , tt ⟩ = foo (λ x → fromFoo (f x))
-- -- fromFoo ⟨ suc () , _ ⟩

