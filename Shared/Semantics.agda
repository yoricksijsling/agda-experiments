
module Shared.Semantics where

open import Prelude

record Semantics {α β : Level}(A : Set α) : Set (α ⊔ lsuc β) where
  field
    {⟦⟧-Type} : Set β
    ⟦_⟧ : A → ⟦⟧-Type
open Semantics {{...}} public
