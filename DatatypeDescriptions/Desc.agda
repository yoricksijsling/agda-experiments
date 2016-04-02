
-- A type of descriptions which directly mappes to actual datatypes

-- Also see OrnamentDT

module DatatypeDescriptions.Desc where

open import Prelude
open import Shared.Semantics

{-

Hybride aanpak gefocust op een duidelijke presentatie naar de gebruiker toe.
Over het algemeen zijn sum-of-products weergaves eenvoudiger, dus dat houden we
aan waar mogelijk met de +, 0, ι en *. Voor dependent types is de ΣK nodig.
De + en 0 zijn vergelijkbaar met een cons en nil om een lijst met constructors
te maken. De + is hierbij dus niet symmetrisch, maar pakt 1 ConDesc en een
DatDesc voor de rest van de constructors.

Door de index equalities in de ι te stoppen kunnen we by construction geen
detagging doen.





VOLGENDE STAP:

Indices, daarna kunnen we algebraic ornaments doen.



-}

Pow : Set → Set₁
Pow I = I → Set

p0 : Fin 0 → Set
p0 ()

p1 : Set → Fin 1 → Set
p1 A zero = A
p1 A (suc ())

p2 : Set → Set → Fin 2 → Set
p2 A B zero = A
p2 A B (suc zero) = B
p2 A B (suc (suc ()))

module Single where
  infixr 3 _`+_

  data DescTag : Set where
    `ctag : DescTag
    `dtag : (#c : Nat) → DescTag

  mutual
    ConDesc : Set₁
    ConDesc = Desc `ctag
    DatDesc : {#c : Nat} → Set₁
    DatDesc {#c} = Desc (`dtag #c)

    data Desc : DescTag → Set₁ where
      ι : ConDesc
      ΣK : (S : Set) → (xs : S → ConDesc) → ConDesc
      rec-*_ : (xs : ConDesc) → ConDesc
      `0 : DatDesc {0}
      _`+_ : ∀{#c}(x : ConDesc) → (xs : DatDesc {#c}) → DatDesc {suc #c}
  {-# DISPLAY Desc `ctag = ConDesc #-}
  {-# DISPLAY Desc (`dtag #c) = DatDesc {#c} #-}

  lookupCtor : ∀{#c}(D : DatDesc {#c}) → Fin #c → ConDesc
  lookupCtor `0 ()
  lookupCtor (x `+ _) zero = x
  lookupCtor (_ `+ xs) (suc k) = lookupCtor xs k

  private
    ⟦_⟧conDesc : ConDesc → Set → Set
    ⟦ ι ⟧conDesc X = ⊤
    ⟦ ΣK S xs ⟧conDesc X = Σ S λ s → ⟦ xs s ⟧conDesc X
    ⟦ rec-* xs ⟧conDesc X = X × ⟦ xs ⟧conDesc X
  ⟦_⟧desc : ∀{dt} → Desc dt → (X : Set) → Set
  ⟦_⟧desc {`ctag} D X = ⟦ D ⟧conDesc X
  ⟦_⟧desc {`dtag #c} D X = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc X

  instance desc-semantics : ∀{dt} → Semantics (Desc dt)
           desc-semantics = record { ⟦_⟧ = ⟦_⟧desc }
  {-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
  {-# DISPLAY ⟦_⟧desc x = ⟦_⟧ x #-}

  data μ {#c : Nat}(F : DatDesc {#c}) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

  K_*_ : Set → ConDesc → ConDesc
  K S * xs = ΣK S (const xs)

  natD : DatDesc
  natD = ι `+ rec-* ι `+ `0

  nat-ex : μ natD  -- `2`
  nat-ex = ⟨ 1 , ⟨ 1 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩

  natlistD : DatDesc
  natlistD = ι `+ (K Nat * rec-* ι) `+ `0

  natlist-ex : μ natlistD  -- 10 ∷ 20 ∷ []`
  natlist-ex = ⟨ 1 , 10 , ⟨ 1 , 20 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩

  -- data AnyFin
    -- anyFin : (n : Nat) → Fin n → AnyFin
  anyfinD : DatDesc
  anyfinD = ΣK Nat (λ n → K (Fin n) * ι) `+ `0

  anyfin-ex : μ anyfinD  -- anyFin 10 9
  anyfin-ex = ⟨ 0 , 10 , 9 , tt ⟩

  Alg : ∀{dt} → Desc dt → Set → Set
  Alg D X = ⟦ D ⟧ X → X

  module Fold {#c : Nat}{D : DatDesc {#c}} {X : Set} (α : Alg D X) where
    mutual      
      fold : μ D → X
      fold ⟨ x ⟩ = α (descmap-fold D x)

      -- Normal map with fold function inlined
      descmap-fold : ∀{dt} (D′ : Desc dt) (xs : ⟦ D′ ⟧ (μ D)) → ⟦ D′ ⟧ X
      descmap-fold ι tt = tt
      descmap-fold (ΣK S xs) (s , v) = s , descmap-fold (xs s) v
      descmap-fold (rec-* xs) (s , v) = fold s , descmap-fold xs v
      descmap-fold `0 (() , _)
      descmap-fold (x `+ xs) (s , v) = s , descmap-fold (lookupCtor (x `+ xs) s) v
  open Fold using (fold) public

  -- descmap : ∀{dt A B} (D : Desc dt) (f : A → B) (v : ⟦ D ⟧ A) → ⟦ D ⟧ B
  -- descmap ι f v = tt
  -- descmap (ΣK S xs) f (s , v) = s , descmap (xs s) f v
  -- descmap (rec-* xs) f (s , v) = f s , descmap xs f v
  -- descmap `0 f (() , _)
  -- descmap (x `+ xs) f (s , v) = s , descmap (lookupCtor (x `+ xs) s) f v

  -- instance desc-functor : ∀{dt}{D : Desc dt} → Functor ⟦ D ⟧
  --          desc-functor {D = D} = record { fmap = descmap D }


module Indices where
  infixr 3 _`+_

  data DescTag : Set where
    `ctag : DescTag
    `dtag : (#c : Nat) → DescTag

  mutual
    ConDesc : Set → Set₁
    ConDesc I = Desc I `ctag
    DatDesc : Set → (#c : Nat) → Set₁
    DatDesc I #c = Desc I (`dtag #c)

    data Desc (I : Set) : DescTag → Set₁ where
      ι : I → ConDesc I
      ΣK : (S : Set) → (xs : S → ConDesc I) → ConDesc I
      rec_*_ : (i : I) → (xs : ConDesc I) → ConDesc I
      `0 : DatDesc I 0
      _`+_ : ∀{#c}(x : ConDesc I) → (xs : DatDesc I #c) → DatDesc I (suc #c)
  {-# DISPLAY Desc I `ctag = ConDesc I #-}
  {-# DISPLAY Desc I (`dtag #c) = DatDesc I #c #-}

  lookupCtor : ∀{I #c} → (D : DatDesc I #c) → Fin #c → ConDesc I
  lookupCtor `0 ()
  lookupCtor (x `+ _) zero = x
  lookupCtor (_ `+ D) (suc k) = lookupCtor D k

  private
    ⟦_⟧conDesc : ∀{I} → ConDesc I → Pow I → Pow I
    ⟦ ι o′ ⟧conDesc X o = o ≡ o′
    ⟦ ΣK S xs ⟧conDesc X o = Σ S λ s → ⟦ xs s ⟧conDesc X o
    ⟦ rec i * xs ⟧conDesc X o = X i × ⟦ xs ⟧conDesc X o
  ⟦_⟧desc : ∀{I dt} → Desc I dt → Pow I → Pow I
  ⟦_⟧desc {dt = `ctag} = ⟦_⟧conDesc
  ⟦_⟧desc {dt = `dtag #c} D X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc X o

  instance desc-semantics : ∀{I dt} → Semantics (Desc I dt)
           desc-semantics = record { ⟦_⟧ = ⟦_⟧desc }
  {-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
  {-# DISPLAY ⟦_⟧desc x = ⟦_⟧ x #-}

  data μ {I : Set}{#c : Nat}(F : DatDesc I #c) (o : I) : Set where
    ⟨_⟩ : ⟦ F ⟧desc (μ F) o → μ F o

  K_*_ : ∀{I} → Set → ConDesc I → ConDesc I
  K S * xs = ΣK S (const xs)

  boolvecD : DatDesc Nat _
  boolvecD = ι 0
          `+ ΣK Nat (λ n → K Bool * rec n * ι (suc n))
          `+ `0

  boolvec-ex : μ boolvecD 2  -- `true ∷ false ∷ []`
  -- boolvec-ex = ⟨ 0 , {!Goal: 2 ≡ 0!} ⟩
  boolvec-ex = ⟨ 1 , _ , true , ⟨ 1 , _ , false , ⟨ zero , refl ⟩ , refl ⟩ , refl ⟩

  finD : DatDesc Nat _
  finD = ΣK Nat (λ n → ι (suc n))
      `+ ΣK Nat (λ n → rec n * ι (suc n))
      `+ `0

  fin-ex : μ finD 1
  -- fin-ex = ⟨ 1 , _ , ⟨ 0 , _ , {!Goal : 0 ≡ suc _203!} ⟩ , refl ⟩
  fin-ex = ⟨ 0 , _ , refl ⟩

  -- Alg : ∀{I #c} → DatDesc I #c → Pow I → Set
  -- Alg {I} D X = {i : I} → ⟦ D ⟧ X i → X i
  Alg : ∀{I dt} → Desc I dt → Pow I → Set
  Alg {I} D X = {i : I} → ⟦ D ⟧ X i → X i

  module Fold {I #c}{D : DatDesc I #c} {X : I → Set} (α : Alg D X) where
    mutual
      fold : {i : I} → μ D i → X i
      fold ⟨ xs ⟩ = α (descmap-fold D xs)

      -- Normal map with fold function inlined
      descmap-fold : ∀{dt i} (D′ : Desc I dt) (xs : ⟦ D′ ⟧ (μ D) i) → ⟦ D′ ⟧ X i
      descmap-fold (ι i) refl = refl
      descmap-fold (ΣK S xs) (s , v) = s , descmap-fold (xs s) v
      descmap-fold (rec i′ * xs) (s , v) = fold {i = i′} s , descmap-fold xs v
      descmap-fold `0 (() , _)
      descmap-fold (x `+ xs) (s , v) = s , descmap-fold (lookupCtor (x `+ xs) s) v
  open Fold using (fold) public

  -- Reornament of bar→barb. The bar→barb ornament can only be implemented with
  -- recons, and in this particular case the forget and reornament should not
  -- break.
  barD : DatDesc ⊤ _
  barD = K (Either Nat Bool) * ι tt `+ `0
  barbD : DatDesc ⊤ _
  barbD = K Nat * ι tt `+ K Bool * ι tt `+ `0
  forget-bar→barb : μ barbD tt → μ barD tt
  forget-bar→barb ⟨ zero , n , refl ⟩ = ⟨ 0 , left n , refl ⟩
  forget-bar→barb ⟨ suc zero , b , refl ⟩ = ⟨ 0 , right b , refl ⟩
  forget-bar→barb ⟨ suc (suc ()) , _ ⟩
  barbiD : DatDesc (μ barD tt) _
  barbiD = ΣK Nat (λ n → ι ⟨ 0 , left n , refl ⟩) `+ ΣK Bool (λ b → ι ⟨ 0 , right b , refl ⟩) `+ `0
  forget-reorn-bar→barb : ∀ bar → μ barbiD bar → μ barD tt
  forget-reorn-bar→barb bar barbi = bar


module Params where
  infixr 3 _`+_

  data ConDesc (#P : Nat) : Set₁ where
    ι : ConDesc #P
    ΣK : (S : Set) → (xs : S → ConDesc #P) → ConDesc #P
    rec-*_ : (xs : ConDesc #P) → ConDesc #P
    par_*_ : (p : Fin #P) → (xs : ConDesc #P) → ConDesc #P

  data Desc (#P : Nat) : Set₁ where
    `0 : Desc #P
    _`+_ : (x : ConDesc #P) → (xs : Desc #P) → Desc #P

  #constructors : ∀{#P} → Desc #P → Nat
  #constructors `0 = 0
  #constructors (_ `+ D) = suc (#constructors D)

  lookupCtor : ∀{#P} → (D : Desc #P) → Fin (#constructors D) → ConDesc #P
  lookupCtor `0 ()
  lookupCtor (x `+ _) zero = x
  lookupCtor (_ `+ D) (suc k) = lookupCtor D k

  ⟦_⟧c : ∀{#P} → ConDesc #P → (env : Fin #P → Set) → (rec : Set) → Set
  ⟦ ι ⟧c env r = ⊤
  ⟦ ΣK S xs ⟧c env r = Σ S λ s → ⟦ xs s ⟧c env r
  ⟦ rec-* xs ⟧c env r = r × ⟦ xs ⟧c env r
  ⟦ par p * xs ⟧c env r = env p × ⟦ xs ⟧c env r

  ⟦_⟧desc : ∀{#P} → Desc #P → (env : Fin #P → Set) → (rec : Set) → Set
  ⟦ D ⟧desc env r = Σ (Fin (#constructors D)) λ k → ⟦ lookupCtor D k ⟧c env r

  data μ {#P : Nat}(F : Desc #P) (env : Fin #P → Set) : Set where
    ⟨_⟩ : ⟦ F ⟧desc env (μ F env) → μ F env

  K_*_ : ∀{#P} → Set → ConDesc #P → ConDesc #P
  K S * xs = ΣK S (const xs)

  listD : Desc 1
  listD = ι
       `+ par 0 * rec-* ι
       `+ `0

  list-ex : μ listD (p1 Nat)
  list-ex = ⟨ 1 , 10 , ⟨ 1 , 20 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩


module ParamsIndices where
  infixr 3 _`+_

  data ConDesc (#P : Nat)(I : Set) : Set₁ where
    ι : I → ConDesc #P I
    ΣK : (S : Set) → (xs : S → ConDesc #P I) → ConDesc #P I
    rec_*_ : (i : I) → (xs : ConDesc #P I) → ConDesc #P I
    par_*_ : (p : Fin #P) → (xs : ConDesc #P I) → ConDesc #P I

  data Desc (#P : Nat)(I : Set) : Set₁ where
    `0 : Desc #P I
    _`+_ : (x : ConDesc #P I) → (xs : Desc #P I) → Desc #P I

  #constructors : ∀{#P I} → Desc #P I → Nat
  #constructors `0 = 0
  #constructors (_ `+ D) = suc (#constructors D)

  lookupCtor : ∀{#P I} → (D : Desc #P I) → Fin (#constructors D) → ConDesc #P I
  lookupCtor `0 ()
  lookupCtor (x `+ _) zero = x
  lookupCtor (_ `+ D) (suc k) = lookupCtor D k

  ⟦_⟧c : ∀{#P I} → ConDesc #P I → (env : Fin #P → Set) → Pow I → Pow I
  ⟦ ι o′ ⟧c env r o = o ≡ o′
  ⟦ ΣK S xs ⟧c env r o = Σ S λ s → ⟦ xs s ⟧c env r o
  ⟦ rec i * xs ⟧c env r o = r i × ⟦ xs ⟧c env r o
  ⟦ par p * xs ⟧c env r o = env p × ⟦ xs ⟧c env r o

  ⟦_⟧desc : ∀{#P I} → Desc #P I → (env : Fin #P → Set) → Pow I → Pow I
  ⟦ D ⟧desc p r o = Σ (Fin (#constructors D)) λ k → ⟦ lookupCtor D k ⟧c p r o

  data μ {#P : Nat}{I : Set} (F : Desc #P I) (env : Fin #P → Set) (o : I) : Set where
    ⟨_⟩ : ⟦ F ⟧desc env (μ F env) o → μ F env o

  K_*_ : ∀{P I} → Set → ConDesc P I → ConDesc P I
  K S * xs = ΣK S (const xs)

  vecD : Desc 1 Nat
  vecD = ι 0
      `+ ΣK Nat (λ n → par 0 * rec n * ι (suc n))
      `+ `0

  vec-ex : μ vecD (p1 Bool) 2
  -- vec-ex = ⟨ 1 , _ , true , ⟨ 0 , {!Goal: 1 ≡ 0!} ⟩ , refl ⟩
  vec-ex = ⟨ 1 , _ , true , ⟨ 1 , _ , false , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩
