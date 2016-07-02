
-- Descriptions waarbij een kleine geinternaliseerde taal wordt
-- gebruikt om constructorargumenten te representeren.

-- Door de interpretatie naar een pattern functor kunnen we ook
-- recursieve argumenten encoden. Hierbij wordt afgedwongen dat `rec`
-- alleen in strict-positive posities voorkomt.

module DatatypeDescriptions.LangDesc where

open import Prelude
open import Shared.Semantics

data Test : Set where
  test : (a b : Test) → (a ≡ b → Test ) → Test

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

-- data _∋_ : (Γ : Cx) (T : O Γ) → Set₁ where
--   top : ∀{Γ T} → (Γ ▷ T) ∋ (λ X → T X ∘ fst)
--   pop : ∀{Γ S T} → Γ ∋ T → (Γ ▷ S) ∋ (λ X → T X ∘ fst)

-- ⟦_⟧∋ : ∀{Γ T} → Γ ∋ T → (X : Set) → (γ : ⟦ Γ ⟧ X) → T X γ
-- ⟦ top ⟧∋ X (γ , t) = t
-- ⟦ pop i ⟧∋ X (γ , s) = ⟦ i ⟧∋ X γ

-- --------------------

-- data RecAllowed : Set where
--   recOk : RecAllowed
--   noRec : RecAllowed

-- data Type (Γ : Cx) : RecAllowed → O Γ → Set₁ where
--   -- lit should never allow rec, because we can not guarantee
--   -- strict-positivity
--   `lit : (f : (γ : ⟦ Γ ⟧ ⊤) → Set) → Type Γ recOk (λ X → {!!})
--   -- `Π : ∀{S T} → Type Γ S → Type (Γ ▷ S) T →
--   --      Type Γ (λ γ → (s : S γ) → curry T γ s)
--   `var : ∀{ra T} → Γ ∋ T → Type Γ ra T



-- ------------------------------------------------------------

-- -- data RecAllowed : Set where
-- --   recOk : RecAllowed
-- --   noRec : RecAllowed

-- -- data ArgTerm : RecAllowed → Set₁ where
-- --   arg : ∀{ra} → Set → ArgTerm ra -- Arbitrary terms
-- --   rec : ArgTerm recOk
-- --   pi : ∀{ra} → ArgTerm noRec → ArgTerm ra → ArgTerm ra
  
-- -- data ConDesc : Set₁ where
-- --   ι : ConDesc
-- --   _⊗_ : (S : ArgTerm recOk) → (xs : ConDesc) → ConDesc

-- -- data DatDesc : Nat → Set₁ where
-- --   `0 : DatDesc 0
-- --   _⊕_ : ∀{#c} (x : ConDesc) (xs : DatDesc #c) → DatDesc (suc #c)

-- -- ⟦_⟧term : ArgTerm noRec → Set
-- -- ⟦ arg S ⟧term = S
-- -- ⟦ pi S T ⟧term = ⟦ S ⟧term → ⟦ T ⟧term

-- -- ⟦_⟧argTerm : ∀{ra} → ArgTerm ra → Set → Set
-- -- ⟦ arg S ⟧argTerm X = S
-- -- ⟦ rec ⟧argTerm X = X
-- -- ⟦ pi S T ⟧argTerm X = ⟦ S ⟧term → ⟦ T ⟧argTerm X

-- -- ⟦_⟧conDesc : ConDesc → Set → Set
-- -- ⟦ ι ⟧conDesc X = ⊤
-- -- ⟦ S ⊗ D ⟧conDesc X = ⟦ S ⟧argTerm X × ⟦ D ⟧conDesc X

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
-- -- -- gecodeerd in ArgTerm. In arbitraire expressies met arg mogen geen
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

