

module DatatypeDescriptions.CxDescOrnament where

open import Prelude
open import Shared.Semantics
open import DatatypeDescriptions.CxDesc as Desc

-- (f ⁻¹ b) contains an a such that (f a ≡ b)
data _⁻¹_ {a b}{A : Set a}{B : Set b}(f : A → B) : B → Set (a ⊔ b) where
  inv : (a : A) → f ⁻¹ (f a)
uninv : ∀{a b}{A : Set a}{B : Set b}{f : A → B}{b : B} → f ⁻¹ b → A
uninv (inv a) = a

inv-eq : ∀{a b}{A : Set a}{B : Set b}{f : A → B}{b : B} → (a : f ⁻¹ b) → f (uninv a) ≡ b
inv-eq (inv a) = refl

inv-∘ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}{f : B → C}{g : A → B}
        {c : C} → (b : f ⁻¹ c) → (a : g ⁻¹ uninv b) → (f ∘ g) ⁻¹ c
inv-∘ (inv _) (inv a) = inv a

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
             (s : (γ : ⟦ Δ ⟧) → S (apply c γ)) → (xs⁺ : ConOrn (cxf-instantiate c s) xs) → ConOrn c (S `* xs)
  data DatOrn : ∀{#c}(D : DatDesc #c) → Set₂ where
    `0 : DatOrn `0
    _`+_ : ∀{#c x xs} → (x⁺ : ConOrn (cxf-id ε) x) (xs⁺ : DatOrn xs) → DatOrn {suc #c} (x `+ xs)

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
                ∀{δ X} → ⟦ conOrnToDesc o ⟧conDesc δ X → ⟦ D ⟧conDesc (apply c δ) X
  conForgetNT ι tt = tt
  conForgetNT (-`* xs⁺) (s , v) = s , conForgetNT xs⁺ v
  conForgetNT (rec-`* xs⁺) (s , v) = s , conForgetNT xs⁺ v
  conForgetNT (insert-K S xs⁺) (s , v) = conForgetNT xs⁺ v
  conForgetNT (insert-rec xs⁺) (s , v) = conForgetNT xs⁺ v
  conForgetNT {c = c} (give-K s xs⁺) v = s _ , conForgetNT xs⁺ v
  forgetNT : ∀{#c}{D : DatDesc #c} (o : DatOrn D) →
             ∀{X} → ⟦ ornToDesc o ⟧datDesc X → ⟦ D ⟧datDesc X
  forgetNT `0 (() , _)
  forgetNT (x⁺ `+ xs⁺) (zero , v) = 0 , conForgetNT x⁺ v
  forgetNT (x⁺ `+ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

  forgetAlg : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → DatAlg (ornToDesc o) (μ D)
  forgetAlg o = ⟨_⟩ ∘ forgetNT o

  forget : ∀{#c}{D : DatDesc #c} (o : DatOrn D) → μ (ornToDesc o) → μ D
  forget o = fold (forgetAlg o)

  ----------------------------------------
  -- Examples

  natD : DatDesc 2
  natD = ι `+ (rec-`* ι) `+ `0
  
  nat→list : DatOrn natD
  nat→list = ι `+ insert-K (const Bool) (rec-`* ι) `+ `0
  t-list : ornToDesc nat→list ≡ (ι `+ const Bool `* rec-`* ι `+ `0)
  t-list = refl


module OrnamentIndicesAndParams where
  open Desc.IndicesAndParams public
  open Cxf public

  -- The `u` function tells us how the ornament changes the indices of the current Desc.
  -- The `c` function specifies how the context outside the current Desc has changed.
  data Orn {I J : Set}(u : J → I) : ∀{Γ Δ dt} (c : Cxf Δ Γ) (D : Desc I Γ dt) → Set₁ where
    ι : ∀{Γ Δ i}{c : Cxf Δ Γ} → (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (apply c δ))) → Orn u c (ι i)
    -`*_ : ∀{Γ Δ S xs}{c : Cxf Δ Γ} → (xs⁺ : Orn u (cxf-both c) xs) → Orn u c (S `* xs)
    rec_`*_ : ∀{Γ Δ i xs}{c : Cxf Δ Γ} →
              (j : (δ : ⟦ Δ ⟧) → u ⁻¹ (i (apply c δ))) → (xs⁺ : Orn u c xs) → Orn u c (rec i `* xs)

    insert-K : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
               (S : ⟦ Δ ⟧ → Set) → (xs⁺ : Orn u (cxf-forget c S) xs) → Orn u c xs
    insert-rec : ∀{Γ Δ}{c : Cxf Δ Γ}{xs : ConDesc I Γ} →
                 (j : ⟦ Δ ⟧ → J) → (xs⁺ : Orn u c xs) → Orn u c xs
    give-K : ∀{Γ Δ S xs}{c : Cxf Δ Γ} →
             -- (s : (γ : ⟦ Γ ⟧) → S γ) → (xs⁺ : Orn u (cxf-instantiate c s) xs) → Orn u c (S `* xs)
             (s : (γ : ⟦ Δ ⟧) → S (apply c γ)) → (xs⁺ : Orn u (cxf-instantiate c s) xs) → Orn u c (S `* xs)

    `0 : ∀{Γ Δ}{c : Cxf Δ Γ} → Orn u c `0
    _`+_ : ∀{Γ Δ #c x}{c : Cxf Δ Γ}{xs : DatDesc I Γ #c} →
           (x⁺ : Orn u c x) (xs⁺ : Orn u c xs) → Orn u c (x `+ xs)

  DefOrn : ∀{I}(J : Set)(u : J → I) {Γ}(Δ : Cx)(c : Cxf Δ Γ) {dt}(D : Desc I Γ dt) → Set₁
  DefOrn J u Δ c D = Orn u c D

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
  open OrnamentSemantics public

  module OrnamentalAlgebra {I J : Set}{u : J → I} where
    forgetNT : ∀{Γ Δ dt}{c : Cxf Δ Γ}{D : Desc I Γ dt} (o : Orn u c D) →
               ∀ {δ X j} → ⟦ o ⟧ δ (X ∘ u) j → ⟦ D ⟧ (apply c δ) X (u j)
    forgetNT {c = c} (ι j) {δ} refl = sym (inv-eq (j δ))
    forgetNT (-`* xs⁺) (s , v) = s , forgetNT xs⁺ v
    forgetNT (rec j `* xs⁺) {δ} {X} (s , v) = transport X (inv-eq (j δ)) s , forgetNT xs⁺ v
    forgetNT (insert-K S xs⁺) (s , v) = forgetNT xs⁺ v
    forgetNT (insert-rec j xs⁺) (s , v) = forgetNT xs⁺ v
    forgetNT (give-K s xs⁺) {δ} v = s δ , forgetNT xs⁺ v
    forgetNT `0 (() , _)
    forgetNT (x⁺ `+ xs⁺) (zero , v) = zero , forgetNT x⁺ v
    forgetNT (x⁺ `+ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

    forgetAlg : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
                ∀{δ} → Alg (ornToDesc o) δ (μ D (apply c δ) ∘ u)
    forgetAlg o = ⟨_⟩ ∘ forgetNT o

    forget : ∀{Γ Δ #c}{c : Cxf Δ Γ}{D : DatDesc I Γ #c} (o : Orn u c D) →
             ∀{δ j} → μ (ornToDesc o) δ j → μ D (apply c δ) (u j)
    forget o = fold (forgetAlg o)
  open OrnamentalAlgebra public

  idOrn : ∀{I Γ dt}{D : Desc I Γ dt} → Orn id (cxf-id Γ) D
  idOrn {dt = `contag} {ι o} = ι (λ γ → inv (o γ))
  idOrn {dt = `contag} {S `* xs} = -`* idOrn
  idOrn {dt = `contag} {rec i `* xs} = rec (λ γ → inv (i γ)) `* idOrn
  idOrn {dt = `dattag _} {`0} = `0
  idOrn {dt = `dattag _} {x `+ xs} = idOrn `+ idOrn

  module AlgebraicOrnament {I : Set}{J : I → Set} where
    -- Interestingly, algebraic ornaments only work when the Algebra is
    -- polymorphic in the datatype parameters. That is because during the
    -- definition of datatypes we do not know the values of the parameters, and
    -- by extension we do not know them in an ornament.
    algOrn : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
             (∀{δ : ⟦ Δ ⟧} → Alg D (apply c δ) J) → DefOrn (Σ I J) fst Δ c D
    algOrn {dt = `contag} {c = c} (ι o) α = ι (λ δ → inv (o (apply c δ) , α refl))
    algOrn {dt = `contag} (S `* xs) α = -`* (algOrn xs (λ {γ} → curry α (top γ)))
    algOrn {dt = `contag} {c = c} (rec i `* xs) α = insert-K (λ δ → J (i (apply c δ))) $
                                                    rec (λ δ → inv (i (apply c (pop δ)) , top δ)) `*
                                                    algOrn xs (λ {γ} {a} → curry α (top γ))
    algOrn {dt = `dattag _} `0 α = `0
    algOrn {dt = `dattag _} (x `+ xs) α = algOrn x (curry α 0) `+ algOrn xs (α ∘ (suc *** id))
  open AlgebraicOrnament public

  module Compose {I J K : Set}{u : J → I}{v : K → J} where
    compose : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ}
      {D : Desc I Γ dt} → (o : Orn u c D) → Orn v d (ornToDesc o) → Orn (u ∘ v) (cxf-∘ c d) D
    compose (ι j) (ι k) = ι (λ _ → inv-∘ (j _) (k _))
    compose (ι j) (insert-K T ys⁺) = insert-K T (compose (ι j) ys⁺)
    compose (ι j) (insert-rec k ys⁺) = insert-rec k (compose (ι j) ys⁺)
    compose (-`* xs⁺) (-`* ys⁺) = -`* (compose xs⁺ ys⁺)
    compose (-`* xs⁺) (insert-K T ys⁺) = insert-K T (compose (-`* xs⁺) ys⁺)
    compose (-`* xs⁺) (insert-rec j ys⁺) = insert-rec j (compose (-`* xs⁺) ys⁺)
    compose (-`* xs⁺) (give-K t ys⁺) = give-K t (compose xs⁺ ys⁺)
    compose (rec j `* xs⁺) (rec k `* ys⁺) = rec (λ _ → inv-∘ (j _) (k _)) `* compose xs⁺ ys⁺
    compose (rec j `* xs⁺) (insert-K T ys⁺) = insert-K T (compose (rec j `* xs⁺) ys⁺)
    compose (rec j `* xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (rec j `* xs⁺) ys⁺)
    compose {d = d} (insert-K S xs⁺) (-`* ys⁺) = insert-K (S ∘ apply d) (compose xs⁺ ys⁺)
    compose (insert-K S xs⁺) (insert-K T ys⁺) = insert-K T (compose (insert-K S xs⁺) ys⁺)
    compose (insert-K S xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (insert-K S xs⁺) ys⁺)
    compose (insert-K S xs⁺) (give-K t ys⁺) = compose xs⁺ ys⁺ -- This can't be right??
    compose (insert-rec j xs⁺) (rec k `* ys⁺) = insert-rec (uninv ∘ k) (compose xs⁺ ys⁺)
    compose (insert-rec j xs⁺) (insert-K T ys⁺) = insert-K T (compose (insert-rec j xs⁺) ys⁺)
    compose (insert-rec j xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (insert-rec j xs⁺) ys⁺)
    compose {d = d} (give-K s xs⁺) ys⁺ = give-K (s ∘ apply d) (compose xs⁺ ys⁺)
    compose `0 `0 = `0
    compose (x⁺ `+ xs⁺) (y⁺ `+ ys⁺) = (compose x⁺ y⁺) `+ (compose xs⁺ ys⁺)
  
    -- compose-sound
  open Compose public


  -- Reornaments currently only work when the original datatype does not have
  -- parameters. To make it work for all datatypes, the indices have to be
  -- dependent on the parameters. (See handwritten notes)
  reornament : ∀{I J Δ}{u : J → I}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
               (o : Orn u c D) → Orn (u ∘ fst) (cxf-∘ c (cxf-id Δ)) D
  reornament o = compose o (algOrn (ornToDesc o) (λ {δ} → forgetAlg o {δ}))


module OrnamentExamples where
  open OrnamentIndicesAndParams
  
  natD : DatDesc ⊤ ε 2
  natD = ι (const tt) `+ rec (const tt) `* ι (const tt) `+ `0
  natD-zero : μ natD tt tt
  natD-zero = ⟨ 0 , refl ⟩
  natD-suc : μ natD tt tt → μ natD tt tt
  natD-suc n = ⟨ 1 , n , refl ⟩
  listD : DatDesc ⊤ (ε ▷Set) 2
  listD = ι (const tt) `+ top `* rec (const tt) `* ι (const tt) `+ `0

  module NatToList where
    nat→list : DefOrn ⊤ id (ε ▷Set) (mk pop) natD
    nat→list = ι (λ δ → inv tt) `+ insert-K top (rec (λ δ → inv tt) `* ι (λ δ → inv tt)) `+ `0
    t-nat→list : ornToDesc nat→list ≡ (ι (const tt) `+ top `* rec (const tt) `* ι (const tt) `+ `0)
    t-nat→list = refl

  module ListToVec where
    list→vec : Orn (λ (j : Nat) → tt) (cxf-id _) listD
    list→vec = ι (λ δ → inv 0) `+
               insert-K (const Nat) (-`* rec (inv ∘ top ∘ pop) `* ι (inv ∘ suc ∘ top ∘ pop)) `+ `0
    t-list→vec : ornToDesc list→vec ≡ (ι (const 0) `+
                                      (const Nat) `* (top ∘ pop) `* rec (top ∘ pop) `* ι (suc ∘ top ∘ pop) `+ `0)
    t-list→vec = refl

  module ListToNatList where
    list-ex : μ listD (tt , Nat) tt
    list-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

    list→natlist : DefOrn ⊤ id ε (mk (_, Nat)) listD
    list→natlist = ι (λ δ → inv tt) `+ (-`* rec (λ δ → inv tt) `* ι (λ δ → inv tt)) `+ `0

    natlist-ex : μ (ornToDesc list→natlist) tt tt
    natlist-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

  module LengthAlgebra where
    lengthAlg : ∀ {A} → Alg listD (tt , A) (λ tt → Nat)
    lengthAlg (zero , refl) = 0
    lengthAlg (suc zero , x , xs , refl) = suc xs
    lengthAlg (suc (suc ()) , _)

    ll : Orn fst (cxf-id _) listD
    ll = algOrn listD lengthAlg

  module ReornamentNatToList where
    open NatToList
  
    nat→vec : Orn (const tt) (mk (const tt)) natD
    nat→vec = reornament nat→list

    t-nat→vec : ornToDesc nat→vec ≡ (ι (const (tt , natD-zero))
      `+ top `* const (μ natD tt tt) `* rec (λ γ → tt , top γ) `* ι (λ γ → tt , natD-suc (top γ))
      `+ `0)
    t-nat→vec = refl

    ex-vec : μ (ornToDesc nat→vec) (tt , Nat) (tt , (natD-suc (natD-suc natD-zero)))
    ex-vec = ⟨ 1 , 33 , _ , ⟨ 1 , 44 , _ , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

    t-forget-vec : forget nat→vec ex-vec ≡ natD-suc (natD-suc natD-zero)
    t-forget-vec = refl
