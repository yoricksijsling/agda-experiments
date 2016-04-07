
module DatatypeDescriptions.ParamsIndicesOrnament where

open import Prelude
open import Shared.Semantics
open import DatatypeDescriptions.Desc as Desc

open Desc.ParamsIndices

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

mutual
  data Orn {E E′}(ef : EnvIndex E′ → EnvIndex E){I J : Set}(u : J → I) :
           ∀{dt} (D : Desc E I dt) → Set₁ where
    ι : ∀{i} → (j : u ⁻¹ i) → Orn ef u (ι i)
    ΣK : ∀ S {xs} → (xs⁺ : ∀ s → Orn ef u (xs s)) → Orn ef u (ΣK S xs)
    rec_*_ : ∀{i xs} → (j : u ⁻¹ i) (xs⁺ : Orn ef u xs) → Orn ef u (rec i * xs)
    Σpar : ∀{e xs} → (e′ : ef ⁻¹ e) (xs⁺ : ∀ s → Orn ef u (xs s)) → Orn ef u (Σpar e xs)

    -- insert-par
    -- give-par should be impossible? 
    insert-rec : ∀{xs} → (j : J) → (xs⁺ : Orn ef u {`ctag} xs) → Orn ef u xs
    insert-ΣK : ∀{xs} → (S : Set) → (xs⁺ : S → Orn ef u {`ctag} xs) → Orn ef u xs
    give-K : ∀{S xs} → (s : S) → (xs⁺ : Orn ef u (xs s)) → Orn ef u (ΣK S xs)

    `0 : Orn ef u `0
    _`+_ : ∀{#c x xs} → (x⁺ : Orn ef u x) (xs⁺ : Orn ef u {`dtag #c} xs) → Orn ef u (x `+ xs)

insert-K_*_ : ∀{E E′}{ef : EnvIndex E′ → EnvIndex E}{I J}{u : J → I} →
              {xs : ConDesc E I} → (S : Set) → (xs⁺ : Orn ef u xs) → Orn ef u xs
insert-K S * xs⁺ = insert-ΣK S (const xs⁺)

K-id-*_ : ∀{E E′}{ef : EnvIndex E′ → EnvIndex E}{I J}{u : J → I}
          {S}{xs : ConDesc E I} → (xs⁺ : Orn ef u xs) → Orn ef u (ΣK S (const xs))
K-id-* xs⁺ = ΣK _ (const xs⁺)


----------------------------------------
-- Semantics

module OrnamentSemantics {E E′}{ef : EnvIndex E′ → EnvIndex E}{I J : Set}{u : J → I} where

  ornToDesc : ∀{dt}{D : Desc E I dt}(o : Orn ef u D) → Desc E′ J dt
  ornToDesc (ι (inv j)) = ι j
  ornToDesc (ΣK S xs⁺) = ΣK S λ s → ornToDesc (xs⁺ s)
  ornToDesc (rec (inv j) * xs⁺) = rec j * ornToDesc xs⁺
  -- ornToDesc (par (inv q) * xs⁺) = par q * ornToDesc xs⁺
  -- ornToDesc (Σpar (inv q) xs⁺) = Σpar q λ s → ornToDesc (xs⁺ s)
  ornToDesc (Σpar (inv e′) xs⁺) = Σpar e′ λ e → ornToDesc (xs⁺ {!!})
  ornToDesc (insert-rec j xs⁺) = rec j * ornToDesc xs⁺
  ornToDesc (insert-ΣK S xs⁺) = ΣK S λ s → ornToDesc (xs⁺ s)
  ornToDesc (give-K s xs⁺) = ornToDesc xs⁺
  ornToDesc `0 = `0
  ornToDesc (x⁺ `+ xs⁺) = ornToDesc x⁺ `+ ornToDesc xs⁺

--   instance orn-semantics : ∀{dt}{D : Desc E I dt} → Semantics (Orn r u D)
--            orn-semantics = record { ⟦_⟧ = ⟦_⟧ ∘ ornToDesc }
-- open OrnamentSemantics


-- ----------------------------------------
-- -- Ornamental algebra

-- module OrnamentalAlgebra {P Q}{r : Fin Q → Fin P}{env : Pow (Fin P)}{I J : Set}{u : J → I} where
--   forgetNT : ∀{dt}{D : Desc P I dt} (o : Orn r u D) →
--              ∀ {X j} → ⟦ o ⟧ (env ∘ r) (X ∘ u) j → ⟦ D ⟧ env X (u j)
--   forgetNT (ι (inv j)) refl = refl
--   forgetNT (ΣK _ xs⁺) (s , v) = s , forgetNT (xs⁺ s) v
--   forgetNT (rec (inv _) * xs⁺) (s , v) = s , forgetNT xs⁺ v
--   -- forgetNT (par (inv _) * xs⁺) (s , v) = s , forgetNT xs⁺ v
--   forgetNT (Σpar (inv _) xs⁺) (s , v) = s , forgetNT (xs⁺ s) v
--   forgetNT (insert-rec j xs⁺) (_ , v) = forgetNT xs⁺ v
--   forgetNT (insert-ΣK _ xs⁺) (s , v) = forgetNT (xs⁺ s) v
--   forgetNT (give-K s xs⁺) v = s , forgetNT xs⁺ v
--   forgetNT `0 (() , _)
--   forgetNT (x⁺ `+ xs⁺) (zero , v) = zero , forgetNT x⁺ v
--   forgetNT (x⁺ `+ xs⁺) (suc k , v) = (suc *** id) (forgetNT xs⁺ (k , v))

--   forgetAlg : ∀{#c}{D : DatDesc P I #c} (o : Orn r u D) → Alg (ornToDesc o) (env ∘ r) (μ D env ∘ u)
--   forgetAlg o = ⟨_⟩ ∘ forgetNT o

--   forget : ∀{#c}{D : DatDesc P I #c} (o : Orn r u D) {j} → μ (ornToDesc o) (env ∘ r) j → μ D env (u j)
--   forget o = fold (forgetAlg o)
-- open OrnamentalAlgebra


-- ----------------------------------------
-- -- Id

-- idOrn : ∀{P I dt}{D : Desc P I dt} → Orn id id D
-- idOrn {D = ι i} = ι (inv i)
-- idOrn {D = ΣK S xs} = ΣK S (λ _ → idOrn)
-- idOrn {D = rec i * xs} = rec (inv i) * idOrn
-- -- idOrn {D = par p * xs} = par (inv p) * idOrn
-- idOrn {D = Σpar p xs} = Σpar (inv p) idOrn
-- idOrn {D = `0} = `0
-- idOrn {D = x `+ xs} = idOrn `+ idOrn

-- listD : DatDesc 1 ⊤ 2
-- listD = ι tt `+ (par 0 * rec tt * ι tt) `+ `0
-- ListD : Set → Set
-- ListD A = μ listD (p1 A) tt
-- ListD-nil : ∀{A} → ListD A
-- ListD-nil = ⟨ 0 , refl ⟩
-- ListD-cons : ∀{A} → A → ListD A → ListD A
-- ListD-cons x xs = ⟨ 1 , x , xs , refl ⟩

-- lengthAlg : ∀{A} → Alg listD (p1 A) (const Nat)
-- lengthAlg (zero , refl) = 0
-- lengthAlg (suc zero , x , xs , refl) = suc xs
-- lengthAlg (suc (suc ()) , _)
-- sumAlg : Alg listD (p1 Nat) (const Nat)
-- sumAlg (zero , refl) = 0
-- sumAlg (suc zero , x , xs , refl) = x + xs
-- sumAlg (suc (suc ()) , _)

-- ----------------------------------------
-- -- Algebraic ornament



-- algOrn : ∀{P env I J dt}(D : Desc P I dt) → Alg D env J → Orn id {J = Σ I J} fst D
-- algOrn (ι i) α = ι (inv (i , α refl))
-- algOrn (ΣK S xs) α = ΣK S λ s → algOrn (xs s) (curry α s)
-- algOrn {J = J} (rec i * xs) α = insert-ΣK (J i) λ j → rec (inv (i , j)) * algOrn xs (curry α j)
-- algOrn {env = env} (par p * xs) α = par (inv p) * (algOrn xs (curry α {!!}))
-- algOrn `0 α = `0
-- algOrn (x `+ xs) α = algOrn x (curry α 0) `+ algOrn xs (α ∘ (suc *** id))
-- -- reindex to K ≅ Σ I J ?

-- -- compose : ∀{I J K}{u : J → I}{v : K → J}{dt}{D : Desc I dt} →
-- --           (o : Orn u D) → Orn v (ornToDesc o) → Orn (u ∘ v) D
-- -- compose (ι (inv _)) (ι (inv k)) = ι (inv k)  
-- -- compose (ι (inv j)) (insert-rec k ys⁺) = insert-rec k (compose (ι (inv j)) ys⁺)
-- -- compose (ι (inv j)) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → (compose (ι (inv j)) (ys⁺ t)))
-- -- compose (ΣK xs⁺) (ΣK ys⁺) = ΣK (λ s → compose (xs⁺ s) (ys⁺ s))
-- -- compose (ΣK xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (ΣK xs⁺) ys⁺)
-- -- compose (ΣK xs⁺) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → compose (ΣK xs⁺) (ys⁺ t))
-- -- compose (ΣK xs⁺) (give-K s ys⁺) = give-K s (compose (xs⁺ s) ys⁺)
-- -- compose (rec (inv _) * xs⁺) (rec (inv k) * ys⁺) = rec (inv k) * (compose xs⁺ ys⁺)
-- -- compose (rec (inv j) * xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (rec (inv j) * xs⁺) ys⁺)
-- -- compose (rec (inv j) * xs⁺) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → compose (rec (inv j) * xs⁺) (ys⁺ t))
-- -- compose (insert-rec _ xs⁺) (rec (inv k) * ys⁺) = insert-rec k (compose xs⁺ ys⁺)
-- -- compose (insert-rec j xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (insert-rec j xs⁺) ys⁺)
-- -- compose (insert-rec j xs⁺) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → compose (insert-rec j xs⁺) (ys⁺ t))
-- -- compose (insert-ΣK S xs⁺) (ΣK ys⁺) = insert-ΣK S (λ s → compose (xs⁺ s) (ys⁺ s))
-- -- compose (insert-ΣK S xs⁺) (insert-rec k ys⁺) = insert-rec k (compose (insert-ΣK S xs⁺) ys⁺)
-- -- compose (insert-ΣK S xs⁺) (insert-ΣK T ys⁺) = insert-ΣK T (λ t → compose (insert-ΣK S xs⁺) (ys⁺ t))
-- -- compose (insert-ΣK S xs⁺) (give-K s ys⁺) = compose (xs⁺ s) ys⁺
-- -- compose (give-K s xs⁺) ys⁺ = give-K s (compose xs⁺ ys⁺)
-- -- compose `0 `0 = `0
-- -- compose (x⁺ `+ xs⁺) (y⁺ `+ ys⁺) = compose x⁺ y⁺ `+ compose xs⁺ ys⁺

-- -- -- compose-sound : ∀{I J K}{u : J → I}{v : K → J}{dt}{D : Desc I dt} →
-- -- --                (o : Orn u D) → (p : Orn v (ornToDesc o)) →
-- -- --                (ornToDesc (compose o p)) ≡ ornToDesc p
-- -- -- boring!

-- -- reornament : ∀{I J}{u : J → I}{#c}{D : DatDesc I #c} →
-- --              (o : Orn u D) → Orn (u ∘ fst) D
-- -- reornament o = compose o (algOrn (ornToDesc o) (forgetAlg o))


-- -- ----------------------------------------
-- -- -- Examples!

-- -- natD : DatDesc ⊤ _
-- -- natD = ι tt `+ rec tt * ι tt `+ `0
-- -- natD-zero : μ natD tt
-- -- natD-zero = ⟨ 0 , refl ⟩
-- -- natD-suc : μ natD tt → μ natD tt
-- -- natD-suc n = ⟨ 1 , n , refl ⟩

-- -- blistD : DatDesc ⊤ _
-- -- blistD = ι tt `+ K Bool * rec tt * ι tt `+ `0
-- -- blistD-nil : μ blistD tt
-- -- blistD-nil = ⟨ 0 , refl ⟩
-- -- blistD-cons : Bool → μ blistD tt → μ blistD tt
-- -- blistD-cons x xs = ⟨ 1 , x , xs , refl ⟩

-- -- module ExampleFin where
-- --   nat→fin : Orn {J = Nat} (const tt) natD
-- --   nat→fin = insert-ΣK Nat (λ n → ι (inv (suc n))) `+
-- --             insert-ΣK Nat (λ n → rec (inv n) * ι (inv (suc n))) `+
-- --             `0

-- --   ex-fin : μ (ornToDesc nat→fin) 5
-- --   ex-fin = ⟨ 1 , _ , ⟨ 1 , _ , ⟨ 0 , _ , refl ⟩ , refl ⟩ , refl ⟩
-- --   ex-fin-forget : forget nat→fin ex-fin ≡ ⟨ 1 , ⟨ 1 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩
-- --   ex-fin-forget = refl


-- -- module ExampleVec where
-- --   blist→bvec : Orn {J = Nat} (const tt) blistD
-- --   blist→bvec = ι (inv 0) `+
-- --                insert-ΣK Nat (λ n → K-id-* rec (inv n) * ι (inv (suc n))) `+
-- --                `0
-- --   test-bvec : ornToDesc blist→bvec ≡ (ι 0 `+ ΣK Nat (λ n → K Bool * rec n * ι (suc n)) `+ `0)
-- --   test-bvec = refl
  
-- --   ex-vec : μ (ornToDesc blist→bvec) 2
-- --   ex-vec = ⟨ 1 , _ , true , ⟨ 1 , _ , false , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩
-- --   ex-vec-forget : forget blist→bvec ex-vec ≡ ⟨ 1 , true , ⟨ 1 , false , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩
-- --   ex-vec-forget = refl


-- -- module ExampleAlgebraicOrnament where
-- --   lengthAlg : Alg blistD (const Nat)
-- --   lengthAlg (zero , refl) = 0
-- --   lengthAlg (suc zero , _ , xs , refl) = suc xs
-- --   lengthAlg (suc (suc ()) , _)

-- --   blist→bvec : Orn fst blistD
-- --   blist→bvec = algOrn blistD lengthAlg
-- --   test-bvec : ornToDesc blist→bvec ≡ (ι (tt , 0) `+
-- --                (K Bool * ΣK Nat λ n → rec (tt , n) * ι (tt , (suc n))) `+ `0)
-- --   test-bvec = refl

-- -- module ExampleReornament where
-- --   nat→blist : Orn id natD
-- --   nat→blist = idOrn `+ insert-K Bool * idOrn `+ `0
-- --   nat→bvec : Orn fst natD
-- --   nat→bvec = reornament nat→blist

-- --   test-blist : ornToDesc nat→blist ≡ (ι tt `+ K Bool * rec tt * ι tt `+ `0)
-- --   test-blist = refl
-- --   test-bvec : ornToDesc nat→bvec ≡ ( ι (tt , natD-zero) `+
-- --     (K Bool * ΣK (μ natD tt) λ n → rec (tt , n) * ι (tt , natD-suc n)) `+
-- --     `0)
-- --   test-bvec = refl
