
module DatatypeDescriptions.IndicesOrnament where

open import Prelude
open import Shared.Semantics
open import DatatypeDescriptions.Desc as Desc

open Desc.Indices

-- (f ⁻¹ b) contains an a such that (f a ≡ b)
data _⁻¹_ {A B : Set}(f : A → B) : Pow B where
  inv : (a : A) → f ⁻¹ (f a)

-- With the original definition of ornaments where one could only add K's and
-- add indices, it made sense to have a mapping (J → I). The mapping specifies
-- that every index (i : I) is refined into many (j : J)'s. A (u ⁻¹ i) means
-- that one of the j's to which this i is connected can be picked. J → I acts
-- as a multivalued function I → J.
-- QUESTION: Do we actually need to restrain which values can be picked? Or is
-- it ok to pick _any_ j? ANSWER: Yes, we do. By restraining the value in this
-- way, every (ι j) can be translated back to a (ι i). Without u we are able
-- to create an ornament where multiple input values are translated to the
-- _same_ output value, making a forget function impossible.

tabulateCtors : ∀{#c I} → (Fin #c → ConDesc I) → DatDesc I #c
tabulateCtors {zero} f = `0
tabulateCtors {suc #c} f = f 0 `+ tabulateCtors (f ∘ suc)

mutual
  data Orn {I J : Set}(u : J → I) : ∀{dt} (D : Desc I dt) → Set₁ where
    ι : ∀{i} → (j : u ⁻¹ i) → Orn u (ι i)
    ΣK : ∀{S xs} → (xs⁺ : (s : S) → Orn u (xs s)) → Orn u (ΣK S xs)
    rec_*_ : ∀{i xs} → (j : u ⁻¹ i) (xs⁺ : Orn u xs) → Orn u (rec i * xs)

    insert-rec : {xs : ConDesc I} → (j : J) → (xs⁺ : Orn u xs) → Orn u xs
    insert-ΣK : {xs : ConDesc I} → (S : Set) → (xs⁺ : S → Orn u xs) → Orn u xs
    give-K : ∀{S xs} → (s : S) → (xs⁺ : Orn u (xs s)) → Orn u (ΣK S xs)

    `0 : Orn u `0
    _`+_ : ∀{#c x}{xs : DatDesc I #c} → (x⁺ : Orn u x) (xs⁺ : Orn u xs) → Orn u (x `+ xs)

insert-K_*_ : ∀{I J}{u : J → I}{xs : ConDesc I} → (S : Set) → (xs⁺ : Orn u xs) → Orn u xs
insert-K S * xs⁺ = insert-ΣK S (const xs⁺)

K-id-*_ : ∀{I J}{u : J → I}{S xs} → (xs⁺ : Orn u xs) → Orn u (ΣK S (const xs))
K-id-* xs⁺ = ΣK (const xs⁺)


----------------------------------------
-- Semantics

module OrnamentSemantics {I J : Set}{u : J → I} where

  ornToDesc : ∀{dt}{D : Desc I dt}(o : Orn u D) → Desc J dt
  ornToDesc (ι (inv j)) = ι j
  ornToDesc (ΣK xs⁺) = ΣK _ λ s → ornToDesc (xs⁺ s)
  ornToDesc (rec (inv j) * xs⁺) = rec j * ornToDesc xs⁺
  ornToDesc (insert-rec j xs⁺) = rec j * ornToDesc xs⁺
  ornToDesc (insert-ΣK S xs⁺) = ΣK S λ s → ornToDesc (xs⁺ s)
  ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
  ornToDesc `0 = `0
  ornToDesc (x⁺ `+ xs⁺) = ornToDesc x⁺ `+ ornToDesc xs⁺

  instance orn-semantics : ∀{dt}{D : Desc I dt} → Semantics (Orn u D)
           orn-semantics = record { ⟦_⟧ = ⟦_⟧ ∘ ornToDesc }
open OrnamentSemantics


----------------------------------------
-- Ornamental algebra

module OrnamentalAlgebra {I J : Set}{u : J → I} where

  forgetNT : ∀{dt}{D : Desc I dt} (o : Orn u D) →
             ∀ {X j} → ⟦ o ⟧ (X ∘ u) j → ⟦ D ⟧ X (u j)
  forgetNT (ι (inv j)) refl = refl
  forgetNT (ΣK xs⁺) (s , v) = s , forgetNT (xs⁺ s) v
  forgetNT (rec (inv _) * xs⁺) (s , v) = s , forgetNT xs⁺ v
  forgetNT (insert-rec j xs⁺) (_ , v) = forgetNT xs⁺ v
  forgetNT (insert-ΣK S xs⁺) (s , v) = forgetNT (xs⁺ s) v
  forgetNT (give-K s xs⁺) v = s , forgetNT xs⁺ v
  forgetNT `0 (() , _)
  forgetNT (x⁺ `+ xs⁺) (zero , v) = zero , forgetNT x⁺ v
  forgetNT (x⁺ `+ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))


  forgetAlg : ∀{#c}{D : DatDesc I #c} (o : Orn u D) → Alg (ornToDesc o) (μ D ∘ u)
  forgetAlg o = ⟨_⟩ ∘ forgetNT o

  forget : ∀{#c}{D : DatDesc I #c} (o : Orn u D) {j} → μ (ornToDesc o) j → μ D (u j)
  forget o = fold (forgetAlg o)
open OrnamentalAlgebra


----------------------------------------
-- Id

idOrn : ∀{I dt}{D : Desc I dt} → Orn id D
idOrn {D = ι i} = ι (inv i)
idOrn {D = ΣK S xs} = ΣK (λ _ → idOrn)
idOrn {D = rec i * xs} = rec (inv i) * idOrn
idOrn {D = `0} = `0
idOrn {D = x `+ xs} = idOrn `+ idOrn


----------------------------------------
-- Algebraic ornament

algOrn : ∀{I J dt}(D : Desc I dt) → Alg D J → Orn {J = Σ I J} fst D
algOrn (ι i) α = ι (inv (i , α refl))
algOrn (ΣK S xs) α = ΣK (λ s → algOrn (xs s) (curry α s))
algOrn {J = J} (rec i * xs) α = insert-ΣK (J i) λ j → rec (inv (i , j)) * algOrn xs (curry α j)
algOrn `0 α = `0
algOrn (x `+ xs) α = algOrn x (curry α 0) `+ algOrn xs (α ∘ (suc *** id))
-- reindex to K ≅ Σ I J ?

compose : ∀{I J K}{u : J → I}{v : K → J}{dt}{D : Desc I dt} →
          (o : Orn u D) → Orn v (ornToDesc o) → Orn (u ∘ v) D
compose (ι (inv _)) (ι (inv k)) = ι (inv k)  
compose (ι (inv j)) (insert-rec k ys⁺) = insert-rec k (compose (ι (inv j)) ys⁺)
compose (ι (inv j)) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → (compose (ι (inv j)) (ys⁺ t)))
compose (ΣK xs⁺) (ΣK ys⁺) = ΣK (λ s → compose (xs⁺ s) (ys⁺ s))
compose (ΣK xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (ΣK xs⁺) ys⁺)
compose (ΣK xs⁺) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → compose (ΣK xs⁺) (ys⁺ t))
compose (ΣK xs⁺) (give-K s ys⁺) = give-K s (compose (xs⁺ s) ys⁺)
compose (rec (inv _) * xs⁺) (rec (inv k) * ys⁺) = rec (inv k) * (compose xs⁺ ys⁺)
compose (rec (inv j) * xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (rec (inv j) * xs⁺) ys⁺)
compose (rec (inv j) * xs⁺) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → compose (rec (inv j) * xs⁺) (ys⁺ t))
compose (insert-rec _ xs⁺) (rec (inv k) * ys⁺) = insert-rec k (compose xs⁺ ys⁺)
compose (insert-rec j xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (insert-rec j xs⁺) ys⁺)
compose (insert-rec j xs⁺) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → compose (insert-rec j xs⁺) (ys⁺ t))
compose (insert-ΣK S xs⁺) (ΣK ys⁺) = insert-ΣK S (λ s → compose (xs⁺ s) (ys⁺ s))
compose (insert-ΣK S xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (insert-ΣK S xs⁺) ys⁺)
compose (insert-ΣK S xs⁺) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → compose (insert-ΣK S xs⁺) (ys⁺ t))
compose (insert-ΣK S xs⁺) (give-K s ys⁺) = compose (xs⁺ s) ys⁺
compose (give-K s xs⁺) ys⁺ = give-K s (compose xs⁺ ys⁺)
compose `0 `0 = `0
compose (x⁺ `+ xs⁺) (y⁺ `+ ys⁺) = compose x⁺ y⁺ `+ compose xs⁺ ys⁺

-- compose-sound : ∀{I J K}{u : J → I}{v : K → J}{dt}{D : Desc I dt} →
--                (o : Orn u D) → (p : Orn v (ornToDesc o)) →
--                (ornToDesc (compose o p)) ≡ ornToDesc p
-- boring!

reornament : ∀{I J}{u : J → I}{#c}{D : DatDesc I #c} →
             (o : Orn u D) → Orn (u ∘ fst) D
reornament o = compose o (algOrn (ornToDesc o) (forgetAlg o))


----------------------------------------
-- Examples!

natD : DatDesc ⊤ _
natD = ι tt `+ rec tt * ι tt `+ `0
natD-zero : μ natD tt
natD-zero = ⟨ 0 , refl ⟩
natD-suc : μ natD tt → μ natD tt
natD-suc n = ⟨ 1 , n , refl ⟩

blistD : DatDesc ⊤ _
blistD = ι tt `+ K Bool * rec tt * ι tt `+ `0
blistD-nil : μ blistD tt
blistD-nil = ⟨ 0 , refl ⟩
blistD-cons : Bool → μ blistD tt → μ blistD tt
blistD-cons x xs = ⟨ 1 , x , xs , refl ⟩

module ExampleFin where
  nat→fin : Orn {J = Nat} (const tt) natD
  nat→fin = insert-ΣK Nat (λ n → ι (inv (suc n))) `+
            insert-ΣK Nat (λ n → rec (inv n) * ι (inv (suc n))) `+
            `0

  ex-fin : μ (ornToDesc nat→fin) 5
  ex-fin = ⟨ 1 , _ , ⟨ 1 , _ , ⟨ 0 , _ , refl ⟩ , refl ⟩ , refl ⟩
  ex-fin-forget : forget nat→fin ex-fin ≡ ⟨ 1 , ⟨ 1 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩
  ex-fin-forget = refl


module ExampleVec where
  blist→bvec : Orn {J = Nat} (const tt) blistD
  blist→bvec = ι (inv 0) `+
               insert-ΣK Nat (λ n → K-id-* rec (inv n) * ι (inv (suc n))) `+
               `0
  test-bvec : ornToDesc blist→bvec ≡ (ι 0 `+ ΣK Nat (λ n → K Bool * rec n * ι (suc n)) `+ `0)
  test-bvec = refl
  
  ex-vec : μ (ornToDesc blist→bvec) 2
  ex-vec = ⟨ 1 , _ , true , ⟨ 1 , _ , false , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩
  ex-vec-forget : forget blist→bvec ex-vec ≡ ⟨ 1 , true , ⟨ 1 , false , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩
  ex-vec-forget = refl


module ExampleAlgebraicOrnament where
  lengthAlg : Alg blistD (const Nat)
  lengthAlg (zero , refl) = 0
  lengthAlg (suc zero , _ , xs , refl) = suc xs
  lengthAlg (suc (suc ()) , _)

  blist→bvec : Orn fst blistD
  blist→bvec = algOrn blistD lengthAlg
  test-bvec : ornToDesc blist→bvec ≡ (ι (tt , 0) `+
               (K Bool * ΣK Nat λ n → rec (tt , n) * ι (tt , (suc n))) `+ `0)
  test-bvec = refl

module ExampleReornament where
  nat→blist : Orn id natD
  nat→blist = idOrn `+ insert-K Bool * idOrn `+ `0
  nat→bvec : Orn fst natD
  nat→bvec = reornament nat→blist

  test-blist : ornToDesc nat→blist ≡ (ι tt `+ K Bool * rec tt * ι tt `+ `0)
  test-blist = refl
  test-bvec : ornToDesc nat→bvec ≡ ( ι (tt , natD-zero) `+
    (K Bool * ΣK (μ natD tt) λ n → rec (tt , n) * ι (tt , natD-suc n)) `+
    `0)
  test-bvec = refl
