
-- Try 'locking' the variables and provide a key where they are allowed to be used.

module DatatypeDescriptions.Lock where

open import Prelude
open import Shared.Semantics

data HetList : List Set → Set₁ where
  [] : HetList []
  _∷_ : ∀{X XS} → (x : X) → (xs : HetList XS) → HetList (X ∷ XS)

module Desc where
  data ConDesc : List Set → Set₁ where
    ι : ∀{vs} → ConDesc vs
    -- ΣK : (S : Set) → (xs : S → ConDesc) → ConDesc
    ΣK : ∀{vs} → (S : HetList vs → Set) → (xs : ConDesc {!!}) → ConDesc vs
    rec-*_ : ∀{vs} (xs : ConDesc vs) → ConDesc vs
  data DatDesc : Nat → Set₁ where
    `0 : DatDesc 0
    _`+_ : ∀{#c}(x : ConDesc [])(xs : DatDesc #c) → DatDesc (suc #c)
  infixr 3 _`+_


open Desc

-- t : DatDesc 1
-- t = (ΣK (λ var → Nat) λ n → {!!}) `+ `0

