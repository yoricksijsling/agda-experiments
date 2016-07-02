
{-# OPTIONS --type-in-type #-}

-- Dybjer and Setzer:
-- A Finite Axiomatization of Inductive-Recursive Definitions

module FiniteInductionRecursion where

open import Prelude hiding (map)

{-

Strictly positive functors can describe types. They can be constructed
with:

  - unit     : F(D) = ⊤
  - argument : F(D) = A × G(D)
  - inductive: F(D) = (A → D) × G(D)

If dependent types are supported, use these rules:

  - unit     : F(D) = ⊤
  - argument  : F(D) = (x : A) × G{x}(D)
  - inductive: F(D) = (A → D) × G(D)

The semantics of Σ-descriptions correspond directly to these rules.

-}

module IndDepSplit where
  F₀ : (D : Set) → Set
  F₀ D = ⊤
  F₁ : (D : Set) → Set
  F₁ D = Σ Nat λ _ → (⊤ → D) × ⊤

  data U : Set where
    intro₀ : F₀ U → U
    intro₁ : F₁ U → U

  F₀-map : ∀{X Y} → (f : X → Y) → F₀ X → F₀ Y
  F₀-map f tt = tt
  F₁-map : ∀{X Y} → (f : X → Y) → F₁ X → F₁ Y
  F₁-map f (x , xs , tt) = x , f ∘ xs , tt


module IndDep where
  F : (D : Set) → Set
  F D = Σ (Fin 2) λ
    { zero → ⊤
    ; (suc zero) → Σ Nat λ _ → (⊤ → D) × ⊤
    ; (suc (suc ()))
    }

  Fmap : ∀{X Y} → (f : X → Y) → F X → F Y
  Fmap f (zero , tt) = 0 , tt
  Fmap f (suc zero , x , xs , tt) = 1 , x , f ∘ xs , tt
  Fmap f (suc (suc ()) , _)

  -- intro
  data U : Set where
    intro : F U → U

  fnil : U
  fnil = intro $ 0 , tt
  fcons : Nat → U → U
  fcons x xs = intro $ 1 , x , const xs , tt

{-

For inductive-recursive, the decoding function is passed as an
argument as well. The following rules apply:

  - unit      : F(U,T) = ⊤
  - dep arg   : F(U,T) = (x : A) × G{x}(U,T)
  - inductive : F(U,T) = (f : A → U) × G{T∘f}(U,T)

F : (D : Set) → Set
Fmap : ∀{U D} → (f : U → D) → F U → F D

-}

module IndRec where

  module Nats where
    Arg : Set
    Arg = Σ (Fin 2) λ
      { zero → ⊤
      ; (suc zero) → Σ (⊤ → ⊤) λ _ → ⊤
      ; (suc (suc ()))
      }

    arg : (U : Set) (T : U → ⊤) → Set
    arg U T = Σ (Fin 2) λ
      { zero → ⊤
      ; (suc zero) → Σ (⊤ → U) λ _ → ⊤
      ; (suc (suc ()))
      }

    map : ∀ U T → arg U T → Arg  -- FArg (U T) ?
    map U T (zero , tt) = zero , tt
    map U T (suc zero , f , tt) = 1 , T ∘ f , tt
    map U T (suc (suc ()) , _)

    mutual
      data U : Set where
        intro : arg U T → U
      T : U → ⊤
      T (intro a) = tt

module AxIndRec where
  data SP (D : Set) : Set where
    nil : SP D
    nonind : (A : Set) → (p : A → SP D) → SP D
    ind : (A : Set) → (p : (A → D) → SP D) → SP D

  Arg : (D : Set) (p : SP D) → Set
  Arg D nil = ⊤
  Arg D (nonind A p) = Σ A λ x → Arg D (p x)
  Arg D (ind A p) = Σ (A → D) λ f → Arg D (p f)

  arg : {D : Set} (p : SP D) (U : Set) (T : U → D) → Set
  arg nil U T = ⊤
  arg (nonind A p) U T = Σ A λ x → arg (p x) U T
  arg (ind A p) U T = Σ (A → U) λ f → arg (p (T ∘ f)) U T

  map : {D : Set} (p : SP D) (U : Set) (T : U → D) →
        (arg p U T) → Arg D p
  map nil U T tt = tt
  map (nonind A p) U T (a , γ) = a , map (p a) U T γ
  map (ind A p) U T (f , γ) = T ∘ f , map (p (T ∘ f)) U T γ

  module Sem {D} (p : SP D) (d : Arg D p → D) where
    mutual
      data U  : Set where
        intro : arg p U T → U

      {-# TERMINATING #-} -- Probably works if map is inlined..
      T : U → D
      T (intro a) = d (map p U T a)

  module Σs where
    -- |SP ⊤| is the degenerate case for inductive definitions (as
    -- opposed to inductive-recursive for |SP D|)
    p : (A : Set) (B : A → Set) → SP ⊤
    p A B = nonind A λ x → nonind (B x) λ y → nil

    open module SemAB (A : Set) (B : A → Set) = Sem (p A B) (const tt)

    to : ∀{A B} → Σ A B → U A B
    to (x , y) = intro (x , y , tt)
    from : ∀{A B} → U A B → Σ A B
    from (intro (x , y , tt)) = x , y

  module Nats where
    p : SP ⊤
    p = nonind Bool λ x → if x
      then nil
      else ind ⊤ (λ _ → nil)

    open Sem p (const tt)
    
    to : Nat → U
    to zero = intro (true , tt)
    to (suc n) = intro (false , const (to n) , tt)
    from : U → Nat
    from (intro (false , n , tt)) = suc (from (n tt))
    from (intro (true , tt)) = zero

  module NΣuniverse where -- a universe closed under N and Σ
    p : SP Set
    p = nonind Bool λ x → if x
      then nil
      else ind ⊤ λ f → ind (f tt) λ y → nil

    d : Arg Set p → Set
    d (true , tt) = Nat
    d (false , A , B , tt) = Σ (A tt) B

    open Sem p d

    `N : U
    `N = intro (true , tt)
    `Σ : (a : U) (b : T a → U) → U
    `Σ a b = intro (false , const a , b , tt)

  module Foo where
    data Wrap {X : Set} (x : X) : Set where
      wrap : Wrap x
    data Foo : Set where
      foo : (x : Foo) → Wrap x → Foo

    p : SP Set
    p = ind ⊤ λ x → nonind (Wrap (x tt)) λ _ → nil

    d : Arg Set p → Set
    d (x , w , tt) = {!!}

    open Sem 
    
    `foo : (x : U p d) → Wrap (T p d x) → U p d
    `foo x w = intro (const x , w , tt)

  module Cxs where
    mutual
      data Cx : Set where
        ε : Cx
        _▷_ : (Γ : Cx) (S : ⟦ Γ ⟧Cx → Set) → Cx
      ⟦_⟧Cx : Cx → Set
      ⟦ ε ⟧Cx = ⊤
      ⟦ Γ ▷ S ⟧Cx = Σ ⟦ Γ ⟧Cx S

    p : SP Set
    p = nonind (Fin 2) λ
      { zero → nil
      ; (suc zero) → ind ⊤ λ ⟦Γ⟧ → nonind (⟦Γ⟧ tt → Set) λ _ → nil
      ; (suc (suc ()))
      }
    d : Arg Set p → Set
    d (zero , tt) = ⊤
    d (suc zero , ⟦Γ⟧ , S , tt) = Σ (⟦Γ⟧ tt) S
    d (suc (suc ()) , _)

    -- open Sem p d

    -- `ε : U
    -- `ε = intro (0 , tt)
    -- _`▷_ : (Γ : U) → (S : T Γ → Set) → U
    -- Γ `▷ S = intro (1 , const Γ , S , tt)
    
    -- cxex : U
    -- cxex = (`ε `▷ const Set) `▷ snd

    -- check-T : T cxex ≡ ⟦ (ε ▷ const Set) ▷ snd ⟧Cx
    -- check-T = refl

    open Sem --renaming (U to μ; T to fun)

    `Cx : Set
    `Cx = U p d
    `⟦_⟧Cx : `Cx → Set
    `⟦_⟧Cx = T p d

    `ε : `Cx
    `ε = intro (0 , tt)
    _`▷_ : (Γ : `Cx) → (S : `⟦_⟧Cx Γ → Set) → `Cx
    Γ `▷ S = intro (1 , const Γ , S , tt)
    
    cxex : `Cx
    cxex = (`ε `▷ const Set) `▷ snd

    check-fun : `⟦ cxex ⟧Cx ≡ ⟦ (ε ▷ const Set) ▷ snd ⟧Cx
    check-fun = refl
