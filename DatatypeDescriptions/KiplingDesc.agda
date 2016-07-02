
{-# OPTIONS --type-in-type #-}

-- We want partial Kipling (from outrageous but meaningful
-- coincidences).. To detect certain terms, but we also want to allow
-- arbitrary agda terms.

module DatatypeDescriptions.KiplingDesc where

open import Prelude

-- K combinator
κ : ∀ {a b } {Γ : Set a } {X : Set b } → X → Γ → X
κ = λ x γ → x

-- S combinator
_§_ : ∀ {a b c} {Γ : Set a } {S : Γ → Set b } {T : (γ : Γ) → S γ → Set c }
  → (f : (γ : Γ) (s : S γ) → T γ s) → (s : (γ : Γ) → S γ)
  → (γ : Γ) → T γ (s γ)
_§_ = λ f s γ → f γ (s γ)

-- uncurry
∨ : ∀ {S T} {P : Σ S T → Set} →
    ((s : S) (t : T s) → P (s , t)) → (st : Σ S T) → P st
∨ p (s , t) = p s t

-- curry
∧ : ∀ {a } {S T } {P : Σ S T → Set a}
  → ((st : Σ S T) → P st) → (s : S) (t : T s) → P (s , t)
∧ p s t = p (s , t)


-- mutual
--   data U : Set₁ where
--     `set : Set → U
--     `Π : (S : U) → (T : El S → U) → U
--   El : U → Set
--   El (`set x) = x
--   El (`Π S T) = (s : El S) → El (T s)

-- Zolang we `Π niet expliciet maken hebben we geen U nodig. U wordt
-- vervangen door Set en El valt weg



mutual
  infixl 4 _▷_
  data Cx : Set₁ where
    ε : Cx
    _▷_ : (Γ : Cx) → (⟦ Γ ⟧Cx → Set) → Cx
  ⟦_⟧Cx : Cx → Set
  ⟦ ε ⟧Cx = ⊤
  ⟦ Γ ▷ S ⟧Cx = Σ ⟦ Γ ⟧Cx λ γ → S γ

data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧Cx → Set) → Set₁ where
  top : ∀{Γ T} → (Γ ▷ T) ∋ (T ∘ fst)
  pop : ∀{Γ S T} → Γ ∋ T → (Γ ▷ S) ∋ (T ∘ fst)

⟦_⟧∋ : ∀{Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧Cx) → T γ
⟦ top ⟧∋ (γ , t) = t
⟦ pop i ⟧∋ (γ , s) = ⟦ i ⟧∋ γ

mutual
  data _⋆_ (Γ : Cx) : (⟦ Γ ⟧Cx → Set) → Set₁ where
    -- Any term can be used as a type
    -- `tmty : ∀{S} → Γ ⊢ S → Γ ⋆ S  -- wrong! The type of a term is used as a type, not very useful
    -- `tmty : ∀{S} → (v : Γ ⊢ S) → Γ ⋆ ⟦ v ⟧⊢  -- This would be better, but it doesn't fit in our types
    -- Give a type manually
    `lit : (f : ⟦ Γ ⟧Cx → Set) → Γ ⋆ f
    `Π : ∀{S T} → Γ ⋆ S → (Γ ▷ S) ⋆ T →
         Γ ⋆ (λ γ → (s : S γ) → ∧ T γ s)
    `Nat : Γ ⋆ const Nat
    `Fin : (v : Γ ⊢ const Nat) → Γ ⋆ (Fin ∘ ⟦ v ⟧⊢)
    `Set : Γ ⋆ const Set
    
  data _⊢_ (Γ : Cx) : (⟦ Γ ⟧Cx → Set) → Set₁ where
    `var : ∀{T} → Γ ∋ T → Γ ⊢ T
    `lit : ∀{P}{p : Γ ⋆ P} → (v : (γ : ⟦ Γ ⟧Cx) → P γ) → Γ ⊢ P

  ⟦_⟧⊢ : ∀{Γ T} → Γ ⊢ T → (γ : ⟦ Γ ⟧Cx) → T γ
  ⟦ `var x ⟧⊢ = ⟦ x ⟧∋
  ⟦ `lit v ⟧⊢ = v


infixr 3 _⊕_
infixr 4 _⊗_ rec-⊗_
data ConDesc : Cx → Set₁ where
  ι : ∀{Γ} → ConDesc Γ
  _⊗_ : ∀{Γ S} → (P : Γ ⋆ S) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
  rec-⊗_ : ∀{Γ}(xs : ConDesc Γ) → ConDesc Γ
data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _⊕_ : ∀{#c} (x : ConDesc ε) (xs : DatDesc #c) → DatDesc (suc #c)

lookupCtor : ∀{#c}(D : DatDesc #c) → Fin #c → ConDesc ε
lookupCtor `0 ()
lookupCtor (x ⊕ _) zero = x
lookupCtor (_ ⊕ xs) (suc k) = lookupCtor xs k

⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧Cx → Set → Set
⟦ ι ⟧conDesc γ X = ⊤
⟦ _⊗_ {S = S} P xs ⟧conDesc γ X = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X
⟦ rec-⊗ xs ⟧conDesc γ X = X × ⟦ xs ⟧conDesc γ X
⟦_⟧datDesc : ∀{#c} → DatDesc #c → Set → Set
⟦_⟧datDesc {#c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc tt X

data μ {#c : Nat}(F : DatDesc #c) : Set where
  ⟨_⟩ : ⟦ F ⟧datDesc (μ F) → μ F



Σ-desc : (A : Set)(B : A → Set) → DatDesc 1
-- Σ-desc A B = `lit (λ γ → A) ⊗ `lit (λ γ → B (snd γ)) ⊗ ι ⊕ `0
Σ-desc A B = `lit (κ A) ⊗ `lit (κ B § snd) ⊗ ι ⊕ `0

-- (S : Set) → (s : S) → Any
any-desc : DatDesc 1
-- any-desc = `lit (κ Set) ⊗ `tmty (`var top) ⊗ ι ⊕ `0
any-desc = `Set ⊗ `lit ⟦ `var top ⟧⊢ ⊗ ι ⊕ `0 -- Use of `lit is cheating.

any-test : μ any-desc
any-test = ⟨ 0 , Nat , {!!} , tt ⟩

someFin-desc : DatDesc 1
someFin-desc = `Nat ⊗ `Fin (`var top) ⊗ ι ⊕ `0
