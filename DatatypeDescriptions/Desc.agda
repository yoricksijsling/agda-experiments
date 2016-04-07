
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

p0 : Pow (Fin 0)
p0 ()

p1 : Set → Pow (Fin 1)
p1 A zero = A
p1 A (suc ())

p2 : Set → Set → Pow (Fin 2)
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
    ConDesc : (I : Set) → Set₁
    ConDesc I = Desc I `ctag
    DatDesc : (I : Set)(#c : Nat) → Set₁
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

  EnvDesc : (#env : Nat)(I : Set){#c : Nat} → Set₁
  EnvDesc #env I {#c} = ((env : Fin #env → Set) → DatDesc I #c)
  
  ⟦_⟧envDesc : ∀{#env I #c}(D : EnvDesc #env I {#c}) (ps : Vec Set #env) (o : I) → Set
  ⟦ D ⟧envDesc ps o = μ (D (indexVec ps)) o

  instance
    envDesc-semantics : ∀{#env I #c} → Semantics (EnvDesc #env I {#c})
    envDesc-semantics = record { ⟦_⟧ = ⟦_⟧envDesc }

  listD : EnvDesc 1 ⊤
  listD env = ι tt `+ (K (env 0) * rec tt * ι tt) `+ `0

  wrapeqD : EnvDesc 1 ⊤
  wrapeqD env = (ΣK (env 0) λ x → ΣK (env 0) λ y → K (x ≡ y) * ι tt) `+ `0
  wrapeqD-eq : ∀{A}(x y : A) → x ≡ y → ⟦ wrapeqD ⟧ (A ∷ []) tt
  wrapeqD-eq x y x=y = ⟨ 0 , x , y , x=y , refl ⟩

  -- THIS FAILS
  countArgs : ConDesc ⊤ → Nat
  countArgs (ι x) = 0
  countArgs (ΣK S xs) = suc (countArgs (xs {!!}))
  countArgs (rec i * xs) = suc (countArgs xs)
  -- Makes sense because you can make nats with one constructor:
  nat1D : EnvDesc 0 ⊤
  nat1D env = (ΣK Bool λ { false → ι tt ; true → rec tt * ι tt }) `+ `0
  -- But in real Agda, this is not allowed:
  --   data Nat1 : Set where
  --     nat1 : (b : Bool) → (λ { false → Nat1 ; true → Nat1 → Nat1 }) b



module Params where
  infixr 3 _`+_

  data ConDesc (#P : Nat) : Set₁ where
    ι : ConDesc #P
    ΣK : (S : Set) → (xs : S → ConDesc #P) → ConDesc #P
    rec-*_ : (xs : ConDesc #P) → ConDesc #P
    Σpar : (p : Fin #P) → (xs : {S : Set} → S → ConDesc #P) → ConDesc #P

  data Desc (#P : Nat) : Set₁ where
    `0 : Desc #P
    _`+_ : (x : ConDesc #P) → (xs : Desc #P) → Desc #P

  data EnvDesc (#P : Nat) : Set₁ where
    mk : (f : (Fin #P → Set) → Desc #P) → EnvDesc #P

  -- data ConDesc {#P}(env : Fin #P → Set) : Set₁ where
  --   ι : ConDesc env
  --   ΣK : (S : Set) → (xs : S → ConDesc env) → ConDesc env
  --   rec-*_ : (xs : ConDesc env) → ConDesc env
  --   Σpar : (p : Fin #P) → (xs : env p → ConDesc env) → ConDesc env
  -- data Desc {#P}(env : Fin #P → Set) : Set₁ where
  --   `0 : Desc env
  --   _`+_ : (x : ConDesc env) → (xs : Desc env) → Desc env
  -- data EnvDesc (#P : Nat) : Set₁ where
  --   mk : (f : {env : Fin #P → Set} → Desc env) → EnvDesc #P

  -- VbD : EnvDesc 1
  -- VbD = mk ((Σpar 0 λ x → Σpar 0 λ y → ΣK (x ≡ y) λ _ → ι) `+ `0)

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
  -- ⟦ par p * xs ⟧c env r = env p × ⟦ xs ⟧c env r
  ⟦ Σpar p xs ⟧c env r = Σ (env p) λ s → ⟦ xs s ⟧c env r

  ⟦_⟧desc : ∀{#P} → Desc #P → (env : Fin #P → Set) → (rec : Set) → Set
  ⟦ D ⟧desc env r = Σ (Fin (#constructors D)) λ k → ⟦ lookupCtor D k ⟧c env r

  data μ {#P : Nat}(F : Desc #P) (env : Fin #P → Set) : Set where
    ⟨_⟩ : ⟦ F ⟧desc env (μ F env) → μ F env

  K_*_ : ∀{#P} → Set → ConDesc #P → ConDesc #P
  K S * xs = ΣK S (const xs)

  par_*_ : ∀{#P} → (p : Fin #P) → (xs : ConDesc #P) → ConDesc #P
  par p * xs = Σpar p (const xs)
  
  listD : Desc 1
  listD = ι `+ par 0 * rec-* ι `+ `0

  data Vb (A : Set) : Set where
    vb : (x : A)(y : A) → x ≡ y → Vb A
  VbD : EnvDesc 1
  VbD = mk λ env → (ΣK (env 0) λ x → ΣK (env 0) λ y → K (x ≡ y) * ι) `+ `0

  list-ex : μ listD (p1 Nat)
  list-ex = ⟨ 1 , 10 , ⟨ 1 , 20 , ⟨ 0 , tt ⟩ , tt ⟩ , tt ⟩


module ParamsIndices where
  -- Env currently only handles parameters of type Set. So the values which are
  -- returned are types. This type can then be used 
  data Env : Set₁ where
    mk : (n : Nat) → (Fin n → Set) → Env
  EnvIndex : Env → Set
  EnvIndex (mk n f) = Fin n
  EnvGet : (E : Env) → EnvIndex E → Set
  EnvGet (mk n f) = f

  data DescTag : Set where
    `ctag : DescTag
    `dtag : (#c : Nat) → DescTag

  mutual
    ConDesc : (E : Env)(I : Set) → Set₁
    ConDesc E I = Desc E I `ctag
    DatDesc : (E : Env)(I : Set)(#c : Nat) → Set₁
    DatDesc E I #c = Desc E I (`dtag #c)

    infixr 3 _`+_
    data Desc (E : Env)(I : Set) : DescTag → Set₁ where
      ι : I → ConDesc E I
      ΣK : (S : Set) → (xs : S → ConDesc E I) → ConDesc E I
      Σpar : (e : EnvIndex E) → (xs : EnvGet E e → ConDesc E I) → ConDesc E I
      rec_*_ : (i : I) → (xs : ConDesc E I) → ConDesc E I
      `0 : DatDesc E I 0
      _`+_ : ∀{#c}(x : ConDesc E I) → (xs : DatDesc E I #c) → DatDesc E I (suc #c)
  {-# DISPLAY Desc I `ctag = ConDesc I #-}
  {-# DISPLAY Desc I (`dtag #c) = DatDesc I #c #-}

  K_*_ : ∀{E I} → Set → ConDesc E I → ConDesc E I
  K S * xs = ΣK S (const xs)

  par_*_ : ∀{E I} → EnvIndex E → ConDesc E I → ConDesc E I
  par e * xs = Σpar e (const xs)

  lookupCtor : ∀{E I #c} → (D : DatDesc E I #c) → Fin #c → ConDesc E I
  lookupCtor `0 ()
  lookupCtor (x `+ _) zero = x
  lookupCtor (_ `+ D) (suc k) = lookupCtor D k

  private
    ⟦_⟧conDesc : ∀{E I} → ConDesc E I → Pow I → Pow I
    ⟦ ι o′ ⟧conDesc X o = o ≡ o′
    ⟦ ΣK S xs ⟧conDesc X o = Σ S λ s → ⟦ xs s ⟧conDesc X o
    -- ⟦_⟧conDesc {E} (Σpar e xs) X o = Σ (EnvGet E e) λ s → ⟦ xs s ⟧conDesc X o
    ⟦ Σpar e xs ⟧conDesc X o = Σ (EnvGet _ e) λ s → ⟦ xs s ⟧conDesc X o
    ⟦ rec i * xs ⟧conDesc X o = X i × ⟦ xs ⟧conDesc X o
  ⟦_⟧desc : ∀{E I dt} → Desc E I dt → Pow I → Pow I
  ⟦_⟧desc {dt = `ctag} = ⟦_⟧conDesc
  ⟦_⟧desc {dt = `dtag #c} D X o = Σ (Fin #c) λ k → ⟦ lookupCtor D k ⟧conDesc X o

  instance desc-semantics : ∀{E I dt} → Semantics (Desc E I dt)
           desc-semantics = record { ⟦_⟧ = ⟦_⟧desc }
  {-# DISPLAY ⟦_⟧conDesc x = ⟦_⟧ x #-}
  {-# DISPLAY ⟦_⟧desc x = ⟦_⟧ x #-}

  data μ {E I #c}(F : DatDesc E I #c) (o : I) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) o → μ F o

  data EnvDesc (#env : Nat)(I : Set){#c : Nat} : Set₁ where
    envDesc : ({f : Fin #env → Set} → DatDesc (mk #env f) I #c) → EnvDesc #env I {#c}

  ⟦_⟧envDesc : ∀{#env I #c}(D : EnvDesc #env I {#c}) (ps : Vec Set #env) (o : I) → Set
  ⟦ envDesc D ⟧envDesc ps o = μ (D {indexVec ps}) o

  instance
    envDesc-semantics : ∀{#env I #c} → Semantics (EnvDesc #env I {#c})
    envDesc-semantics = record { ⟦_⟧ = ⟦_⟧envDesc }

  Alg : ∀{E I dt} → Desc E I dt → Pow I → Set
  Alg {E} {I} D X = {i : I} → ⟦ D ⟧ X i → X i

  module Fold {E I #c}{D : DatDesc E I #c}{X : I → Set} (α : Alg D X) where
    mutual
      fold : {i : I} → μ D i → X i
      fold ⟨ xs ⟩ = α (descmap-fold D xs)

      -- Normal map with fold function inlined
      descmap-fold : ∀{dt i} (D′ : Desc E I dt) (xs : ⟦ D′ ⟧ (μ D) i) → ⟦ D′ ⟧ X i
      descmap-fold (ι i) refl = refl
      descmap-fold (ΣK S xs) (s , v) = s , descmap-fold (xs s) v
      descmap-fold (Σpar p xs) (s , v) = s , descmap-fold (xs s) v
      descmap-fold (rec i′ * xs) (s , v) = fold {i = i′} s , descmap-fold xs v
      descmap-fold `0 (() , _)
      descmap-fold (x `+ xs) (s , v) = s , descmap-fold (lookupCtor (x `+ xs) s) v
  open Fold using (fold) public


  ----------------------------------------
  -- Examples!
    
  natD : EnvDesc 0 ⊤
  natD = envDesc (ι tt `+ rec tt * ι tt `+ `0)
  natD-zero : ⟦ natD ⟧ [] tt
  natD-zero = ⟨ 0 , refl ⟩
  natD-suc : ⟦ natD ⟧ [] tt → ⟦ natD ⟧ [] tt
  natD-suc n = ⟨ 1 , n , refl ⟩

  listD : EnvDesc 1 ⊤
  listD = envDesc (ι tt `+ (par 0 * rec tt * ι tt) `+ `0)
  listD-nil : ∀{A} → ⟦ listD ⟧ (A ∷ []) tt
  listD-nil = ⟨ 0 , refl ⟩
  listD-cons : ∀{A} → A → ⟦ listD ⟧ (A ∷ []) tt → ⟦ listD ⟧ (A ∷ []) tt
  listD-cons x xs = ⟨ 1 , x , xs , refl ⟩

  vecD : EnvDesc 1 Nat
  vecD = envDesc (ι 0 `+ (ΣK Nat λ n → par 0 * rec n * ι (suc n)) `+ `0)
  vecD-nil : ∀{A} → ⟦ vecD ⟧ (A ∷ []) 0
  vecD-nil = ⟨ 0 , refl ⟩
  vecD-cons : ∀{A n} → A → ⟦ vecD ⟧ (A ∷ []) n → ⟦ vecD ⟧ (A ∷ []) (suc n)
  vecD-cons x xs = ⟨ 1 , _ , x , xs , refl ⟩

  wrapeqD : EnvDesc 1 ⊤
  wrapeqD = envDesc ((Σpar 0 λ x → Σpar 0 λ y → K (x ≡ y) * ι tt) `+ `0)
  wrapeqD-eq : ∀{A}(x y : A) → x ≡ y → ⟦ wrapeqD ⟧ (A ∷ []) tt
  wrapeqD-eq x y x=y = ⟨ 0 , x , y , x=y , refl ⟩


  alistD : ∀{Node} → DatDesc (mk 1 (p1 Node)) ⊤ 2
  alistD = ι tt `+ (par 0 * rec tt * ι tt) `+ `0
  ablistD : ∀{Node Leaf} → DatDesc (mk 2 (p2 Node Leaf)) ⊤ 2
  ablistD = (par 1 * ι tt) `+ (par 0 * rec tt * ι tt) `+ `0
