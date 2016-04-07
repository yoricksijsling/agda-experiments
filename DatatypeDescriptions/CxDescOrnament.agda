

module DatatypeDescriptions.CxDescOrnament where

open import Prelude
open import Shared.Semantics
open import DatatypeDescriptions.CxDesc as Desc

-- (f ⁻¹ b) contains an a such that (f a ≡ b)
data _⁻¹_ {A B : Set}(f : A → B) : Pow B where
  inv : (a : A) → f ⁻¹ (f a)
uninv : ∀{A B}{f : A → B}{b : B} → f ⁻¹ b → A
uninv (inv a) = a

inv-conv : ∀{A B}{b : B}{f : A → B} → (a : f ⁻¹ b) → f (uninv a) ≡ b
inv-conv (inv a) = refl

module SimpleOrnament where
  open Desc.Simple
  open Cxf

  data ConOrn : ∀{Γ Δ} (f : Cxf Δ Γ) (D : ConDesc Γ) → Set₂ where
    ι : ∀{Γ Δ}{c : Cxf Δ Γ} → ConOrn c ι
    -`*_ : ∀{Γ Δ S xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn (cxf-both c) xs) → ConOrn c (S `* xs)
    rec-`*_ : ∀{Γ Δ xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn c xs) → ConOrn c (rec-`* xs)

    insert-K : ∀{Γ Δ xs}{c : Cxf Δ Γ} →
               (S : ⟦ Δ ⟧ → Set) → (xs⁺ : ConOrn (cxf-forget c S) xs) → ConOrn c xs
    insert-rec : ∀{Γ Δ xs}{c : Cxf Δ Γ} → (xs⁺ : ConOrn c xs) → ConOrn c xs

    give-K : ∀{Γ Δ S xs}{c : Cxf Δ Γ} →
             (s : (γ : ⟦ Γ ⟧) → S γ) → (xs⁺ : ConOrn (cxf-instantiate c s) xs) → ConOrn c (S `* xs)
  data DatOrn : ∀{#c}(D : DatDesc #c) → Set₂ where
    `0 : DatOrn `0
    _`+_ : ∀{#c x xs} → (x⁺ : ConOrn cxf-ε x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x `+ xs)

  conOrnToDesc : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} → ConOrn c D → ConDesc Δ
  conOrnToDesc ι = ι
  conOrnToDesc (-`*_ {S = S} {c = c} xs⁺) = S ∘ apply c `* conOrnToDesc xs⁺
  conOrnToDesc (rec-`* xs⁺) = rec-`* (conOrnToDesc xs⁺)
  conOrnToDesc (insert-K S xs⁺) = S `* (conOrnToDesc xs⁺)
  conOrnToDesc (insert-rec xs⁺) = rec-`* (conOrnToDesc xs⁺)
  conOrnToDesc (give-K s xs⁺) = conOrnToDesc xs⁺
  ornToDesc : ∀{#c}{D : DatDesc #c} → DatOrn D → DatDesc #c
  ornToDesc `0 = `0
  ornToDesc (x⁺ `+ xs⁺) = conOrnToDesc x⁺ `+ ornToDesc xs⁺

  conForgetNT : ∀{Γ Δ}{c : Cxf Δ Γ}{D : ConDesc Γ} (o : ConOrn c D) →
                ∀ δ X → ⟦ conOrnToDesc o ⟧conDesc δ X → ⟦ D ⟧conDesc (apply c δ) X
  conForgetNT ι δ X tt = tt
  conForgetNT (-`* xs⁺) δ X (s , v) = s , conForgetNT xs⁺ (δ , s) X v
  conForgetNT (rec-`* xs⁺) δ X (s , v) = s , conForgetNT xs⁺ δ X v
  conForgetNT (insert-K S xs⁺) δ X (s , v) = conForgetNT xs⁺ (δ , s) X v
  conForgetNT (insert-rec xs⁺) δ X (s , v) = conForgetNT xs⁺ δ X v
  conForgetNT {c = c} (give-K s xs⁺) δ X v = s (apply c δ) , conForgetNT xs⁺ δ X v

  -- (fold is not implemnted)
  
  ----------------------------------------
  -- Examples

  natD : DatDesc 2
  natD = ι `+ (rec-`* ι) `+ `0
  
  nat→list : DatOrn natD
  nat→list = ι `+ insert-K (const Bool) (rec-`* ι) `+ `0
  t-list : ornToDesc nat→list ≡ (ι `+ const Bool `* rec-`* ι `+ `0)
  t-list = refl




module OrnamentIndicesAndParams where
  open Desc.IndicesAndParams
  open Cxf

  data Orn {I J : Set}(u : J → I) : ∀{Γ Δ dt} (f : Cxf Δ Γ) (D : Desc I Γ dt) → Set₁ where
    ι : ∀{Γ Δ i}{c : Cxf Δ Γ} →
        (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (apply c δ))) → Orn u c (ι i)
    -`*_ : ∀{Γ Δ S xs}{c : Cxf Δ Γ} → (xs⁺ : Orn u (cxf-both c) xs) → Orn u c (S `* xs)
    rec_`*_ : ∀{Γ Δ i xs}{c : Cxf Δ Γ} →
              (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (apply c δ))) → (xs⁺ : Orn u c xs) → Orn u c (rec i `* xs)

    insert-K : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
               (S : ⟦ Δ ⟧ → Set) → (xs⁺ : Orn u (cxf-forget c S) xs) → Orn u c xs
    insert-rec : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
                 (j : ⟦ Δ ⟧ → J) → (xs⁺ : Orn u c xs) → Orn u c xs
    give-K : ∀{Γ Δ S xs}{c : Cxf Δ Γ} →
             (s : (γ : ⟦ Γ ⟧) → S γ) → (xs⁺ : Orn u (cxf-instantiate c s) xs) → Orn u c (S `* xs)

    `0 : ∀{Γ Δ}{c : Cxf Δ Γ} → Orn u c `0
    _`+_ : ∀{Γ Δ #c x}{c : Cxf Δ Γ}{xs : DatDesc I Γ #c} →
           (x⁺ : Orn u c x) (xs⁺ : Orn u c xs) → Orn u c (x `+ xs)


  module OrnamentSemantics {I J : Set}{u : J → I} where
    ornToDesc : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} → (o : Orn u c D) → Desc J Δ dt
    ornToDesc {c = c} (ι j) = ι (uninv ∘ j)
    ornToDesc (-`*_ {S = S} {c = c} xs⁺) = S ∘ apply c `* ornToDesc xs⁺
    ornToDesc (rec j `* xs⁺) = rec (uninv ∘ j) `* ornToDesc xs⁺
    ornToDesc (insert-K S xs⁺) = S `* ornToDesc xs⁺
    ornToDesc (insert-rec j xs⁺) = rec j `* ornToDesc xs⁺
    ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
    ornToDesc `0 = `0
    ornToDesc (x⁺ `+ xs⁺) = ornToDesc x⁺ `+ ornToDesc xs⁺

    instance orn-semantics : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} → Semantics (Orn u c D)
             orn-semantics = record { ⟦_⟧ = ⟦_⟧ ∘ ornToDesc }
  open OrnamentSemantics


  module OrnamentalAlgebra {I J : Set}{u : J → I} where
    forgetNT : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} (o : Orn u c D) →
               ∀ {δ X j} → ⟦ o ⟧ δ (X ∘ u) j → ⟦ D ⟧ (apply c δ) X (u j)
    forgetNT (ι j) {δ} refl = sym (inv-conv (j δ))
    forgetNT (-`* xs⁺) (s , v) = s , forgetNT xs⁺ v
    forgetNT (rec j `* xs⁺) {δ} {X} (s , v) = transport X (inv-conv (j δ)) s , forgetNT xs⁺ v
    forgetNT (insert-K S xs⁺) (s , v) = forgetNT xs⁺ v
    forgetNT (insert-rec j xs⁺) (s , v) = forgetNT xs⁺ v
    forgetNT {c = c} (give-K s xs⁺) {δ} v = s (apply c δ) , forgetNT xs⁺ v
    forgetNT `0 (() , _)
    forgetNT (x⁺ `+ xs⁺) (zero , v) = zero , forgetNT x⁺ v
    forgetNT (x⁺ `+ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

    forgetAlg : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
                ∀{δ} → Alg (ornToDesc o) δ (μ D (apply c δ) ∘ u)
    forgetAlg o = ⟨_⟩ ∘ forgetNT o

    forget : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
             ∀{δ j} → μ (ornToDesc o) δ j → μ D (apply c δ) (u j)
    forget o = fold (forgetAlg o)
  open OrnamentalAlgebra


  idOrn : ∀{I Γ dt}{D : Desc I Γ dt} → Orn id cxf-id D
  idOrn {dt = `contag} {ι o} = ι (λ δ → inv (o δ))
  idOrn {dt = `contag} {S `* xs} = -`* {!idOrn!}
  idOrn {dt = `contag} {rec i `* xs} = {!!}
  idOrn {dt = `dattag .0} {`0} = {!!}
  idOrn {dt = `dattag _} {x `+ xs} = {!!}


  algOrn : ∀{I J Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           ∀{γ} → Alg D γ J → Orn {J = Σ I J} fst c D
  algOrn {dt = `contag} (ι o) α = ι (λ δ → inv ({!!} , {!α refl!}))
  algOrn {dt = `contag} (S `* xs) α = -`* (algOrn xs (curry α {!\!}))
  algOrn {dt = `contag} (rec i `* xs) α = {!!}
  algOrn {dt = `dattag .0} `0 α = {!!}
  algOrn {dt = `dattag _} (x `+ xs) α = {!!}
    

  natD : DatDesc ⊤ ε 2
  natD = ι (const tt) `+ rec (const tt) `* ι (const tt) `+ `0
  nat→list : Orn id {Δ = ε ▷Set} (mk pop) natD
  nat→list = ι (λ δ → inv tt) `+ insert-K top (rec (λ δ → inv tt) `* ι (λ δ → inv tt)) `+ `0
  t-nat→list : ornToDesc nat→list ≡ (ι (const tt) `+ top `* rec (const tt) `* ι (const tt) `+ `0)
  t-nat→list = refl

  listD : DatDesc ⊤ (ε ▷Set) 2
  listD = ι (const tt) `+ top `* rec (const tt) `* ι (const tt) `+ `0
  list→vec : Orn (λ (j : Nat) → tt) cxf-id listD
  list→vec = ι (λ δ → inv 0) `+
             insert-K (const Nat) (-`* rec (λ δ → inv (top (pop δ))) `* ι (λ δ → inv (suc (top (pop δ))))) `+ `0
  t-list→vec : ornToDesc list→vec ≡ (ι (const 0) `+
                                    (const Nat) `* {!ornToDesc list→vec!} `* rec (top ∘ pop) `* ι (suc ∘ top ∘ pop) `+ `0)
  t-list→vec = refl

  
