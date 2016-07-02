{-# OPTIONS --type-in-type #-}

-- A desc type which carries a little environment around

module DatatypeDescriptions.EnvDesc where

open import Prelude
open import Shared.Semantics

Pow : Set → Set₁
Pow I = I → Set


data Foo : Set₁ where
  wrapEq : {A : Set}(x y : A) → x ≡ y → Foo
  someFin : {n : Nat} → Fin n → Foo

module Blob where
  private
    A : Set
    A = ⊤
    B : (a : A) → Set
    B a = Nat
    C : (a : A) → (b : B a) → Set
    C a b = Fin b
    D : (a : A) → (b : B a) → (c : C a b) → Set
    D a b c = Bool
    
  data Blob : Set where
    blob : ⊤ → (n : Nat) → Fin n → Bool → Blob
    blob′ : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → Blob
  -- The user must provide A,B,C,D, so we must ask for values of types Set, A → Set, A → B a → Set ...
  -- blob′D = K Nat * K (λ n → Fin n) * K (λ n k → Bool) * ι
  -- blob′D = ΣK Nat λ n → ΣK (Fin n) λ k → ΣK Bool λ _ → ι


-- infixl 4 _then_
-- mutual
--   data Env : Set₁ where
--     start : Env
--     _then_ : (t : Env)(f : ⟦ t ⟧ee) → Env
  -- ⟦_⟧ee : Env → Set₁
  -- ⟦ env ⟧ee = ⟦ env ⟧e → Set
  -- ⟦_⟧e : Env → Set
  -- ⟦ start ⟧e                      =                                                              ⊤
  -- ⟦ start then A ⟧e               = Σ (A tt) λ a →                                               ⊤
  -- ⟦ start then A then B ⟧e        = Σ (A tt) λ a → Σ (B (a , tt)) λ b →                          ⊤
  -- ⟦ start then A then B then C ⟧e = Σ (A tt) λ a → Σ (B (a , tt)) λ b → Σ (C (a , b , tt)) λ c → ⊤
  -- ⟦ otherwise ⟧e = {!!}

  -- ⟦_⟧ee : Env → Set₁
  -- -- ⟦ env ⟧ee = (fst ⟦ env ⟧e) ⊤ → Set
  -- ⟦ env ⟧ee = {!!} -- fst (⟦ env ⟧e (⊤ , tt)) → Set
  -- ⟦_⟧e : Env → (Set → Σ Set (λ X → X → Set)) → Set → Set
  -- ⟦ start ⟧e                      f X = {!f X!}
  -- ⟦ start then A ⟧e               f X = {!!}
  -- -- ⟦ start then A then B ⟧e        (X , x) = {!!}
  -- -- ⟦ start then A then B then C ⟧e (X , x) = {!!}
  -- ⟦ otherwise ⟧e = {!!}

  -- ⟦_⟧ee : Env → Set₁
  -- ⟦ env ⟧ee = ⟦ env ⟧e → Set
  -- ⟦_⟧e : Env → Set
  -- ⟦ start ⟧e = ⊤
  -- ⟦ start then A ⟧e = Σ ⊤ λ s → A s
  -- ⟦ start then A then B ⟧e = Σ ⊤ λ s → Σ (A s) λ a → B (s , a)
  -- ⟦ start then A then B then C ⟧e = Σ ⊤ λ s → Σ (A s) λ a → Σ (B (s , a)) λ b → C (s , a , b)
  -- ⟦ otherwise ⟧e = {!!}

  -- ⟦_⟧ee : Env → Set₁
  -- ⟦ start ⟧ee = Set
  -- ⟦ start then A ⟧ee = A → Set
  -- ⟦ start then A then B ⟧ee = (a : A) → B a → Set
  -- ⟦ start then A then B then C ⟧ee = (a : A) → (b : B a) → C a b → Set
  -- ⟦ env then A then B then C then D ⟧ee = {!!}

-- t-env : Env
-- t-env = start then (λ { tt → Nat}) then (λ { (n , tt) → Fin n }) then (λ { (n , k , tt) → Bool})
-- t-env : Env
-- t-env = start then (λ s → Nat) then (λ {(s , a) → Fin a}) then (λ { (s , a , b) → Bool })
-- t-env : Env
-- t-env = start then Nat then (λ a → Fin a) then (λ a b → Bool )

-- 

-- postulate
--   A : ⊤ → Set
--   B : (A tt × ⊤) → Set

  

-- prefix0 : {Q : Set}(q : Q) → Q
-- prefix0 q = q
-- Prefix0 : (⊤ → Set) → Set
-- Prefix0 X = X tt
-- t0 : Prefix0 (const ⊤) ≡ ⊤
-- t0 = refl

-- PrefixA : ((a : A tt) → Set) → Set
-- PrefixA X = Prefix0 λ t → Σ (A (prefix0 tt)) λ a →
--             X (prefix0 a)
-- -- prefixa : (v : A tt){Q : Set}(q : Q) → Σ (A tt) λ a → Q
-- prefixa : (v : A tt){Q : A tt → Set}(q : Q v) → Σ (A tt) λ a → Q v
-- prefixa v q = prefix0 (v , q)

-- --       Σ (A tt) (λ a → Σ (B (x , tt)) (λ v → .Q))
-- -- Goal: Σ (A tt) (λ a → Σ (B (a , tt)) (λ b → .Q))
-- -- ————————————————————————————————————————————————————————————
-- -- q  : .Q
-- -- .Q : Set
-- -- v  : Σ (A tt) (λ a → B (a , tt))
-- prefixb : (v : Σ (A tt) λ a → B (a , tt)){Q : Set}(q : Q) → Σ (A tt) λ a → Σ (B (a , tt)) λ b → Q
-- -- Σ (B (x , tt)) (λ v → .Q)
-- prefixb (x , y) {Q} q = {!prefixa x {λ x → B (x , tt) × Q} (y , q)!}
-- -- PrefixB : ((prefixb : {Q : Set}(q : Q) → Σ (A tt) λ a → Σ (B (a , tt)) λ b → Q)
-- --                     → Set) → Set
-- -- PrefixB X = PrefixA λ a prefixa → Σ (B (prefixa a tt)) λ b →
-- --             X (λ q → {!prefixa a tt!}) --(λ q → prefixa (b , q))



--------------------------------------------------
-- Prefix0 : ((prefix0 : {Q : Set}(q : Q) → Q) → Set) → Set
-- Prefix0 X = X (λ q → q)
-- t0 : Prefix0 (const ⊤) ≡ ⊤
-- t0 = refl

-- PrefixA : ((prefixa : ∀{Q}(q : Q) → Σ (A tt) (λ x → Q))   -- Q should be dependent on x ??
-- -- PrefixA : ((prefixa : {Q : Set}(q : Q) → Prefix0 (λ prefix0 → Σ (A (prefix0 tt)) λ a → Q))
--                     → Set) → Set
-- PrefixA X = Prefix0 (λ prefix0 → Σ (A (prefix0 tt)) λ a →
--             X (λ q → prefix0 (a , q)))

-- -- PrefixB : ((prefixb : ∀{Q}(q : Q) → Σ (A tt) λ a → Σ (B ({!!})) λ b → Q)
-- PrefixB : ((prefixb : ∀{Q}(q : Q) → PrefixA (λ prefixa → Σ (B (prefixa tt)) (λ b → Q)))
--                     → Set) → Set
-- PrefixB X =  PrefixA (λ prefixa → Σ (B (prefixa tt)) λ b → X (λ q → {!prefixa (b , q)!})) 

-- Goal            : Σ (A tt) (λ a → Σ (B (a , tt)) (λ v → .Q))
-- ————————————————————————————————————————————————————————————  prefixa tt does not reduce
-- prefixa (b , q) : Σ (A tt) (λ a → Σ (B (prefixa tt)) (λ v → .Q))

-- PrefixA geeft een Σ, waardoor de a superlaat mag worden gekozen, terwijl deze van te voren bepaald moet zijn..
-- prefixa tt wordt niet gereduced, terwijl dit binnen PrefixA gewoon zou moeten kunnen??


-- Goal            : Σ (A tt) (λ a → Σ (?4) (?5))
-- ---
-- prefixa         : {Q : Set} → Q → Σ (A tt) (λ a → Q)
-- prefixa (b , q) : Σ (A tt) (λ a → Σ (B (prefixa tt)) (λ v → .Q))


------------------------------
-- The DepList class takes an accumulating value and can use it to determine the
-- type of x. Note that there is only one function B which determines the type
-- of x.
-- data SumList : Nat → Set where
--   [] : ∀{sum} → SumList sum
--   _∷_ : ∀{sum} → (x : Fin sum) → (xs : SumList (finToNat x + sum)) → SumList sum

-- data DepList {a b}{A : Set a}(B : A → Set b)(f : (acc : A) → B acc → A) : A → Set (a ⊔ b) where
--   [] : ∀{acc} → DepList B f acc
--   _∷_ : ∀{acc} → (x : B acc) → (xs : DepList B f (f acc x)) → DepList B f acc
-- SumList : Nat → Set
-- SumList = DepList Fin (λ acc x → finToNat x + acc)
-- sumlist-ex : SumList 2
-- sumlist-ex = 1 ∷ 2 ∷ 3 ∷ 7 ∷ []
-- sumlist-sum : ∀{sum} → SumList sum → Nat
-- sumlist-sum {sum} [] = sum
-- sumlist-sum (x ∷ xs) = sumlist-sum xs

-- data HetList : List Set → Set₁ where
--   [] : HetList []
--   _∷_ : ∀{X XS} → (x : X) → (xs : HetList XS) → HetList (X ∷ XS)


{-
Kan dit met een DepList?

tylist = ⊤ ∷                 <-- Set
         λ tt → Nat ∷        <-- ⊤ → Set
         λ tt n → Fin n ∷    <-- ⊤ → Nat → Set
         λ tt n k → Bool ∷    <-- ⊤ → (n : Nat) → Fin n → Set
         []

tylist = A ∷         <-- Set
         B ∷         <-- (a : A) → Set
         C ∷         <-- (a : A) → ((b : B a) → Set)
         D           <-- (a : A) → ((b : B a) → ((c : C a b) → Set))
tylist = A ∷         <-- HetList [] → Set
         B ∷         <-- HetList (a    ∷ []) → Set
                       :          A []
         C ∷         <-- HetList (a    ∷ b          ∷ []) → Set
                       :          A []   B (a ∷ [])
         D           <-- HetList (a    ∷ b          ∷ c              ∷ []) → Set
                       :          A []   B (a ∷ [])   C (a ∷ b ∷ [])
         
tylist = λ [] → Nat ∷           <-- HetList [] → Set
         λ (n ∷ []) → Fin n ::  <-- HetList ((λ [] → Nat) [] ∷ []) → Set
         λ (n ∷ k ∷ []) → Bool  <-- HetList ((λ [] → Nat) [] ∷ (λ (n ∷ []) → Fin n) ((λ [] → Nat) [] ∷ [])  ∷ []) → Set
                                  = HetList (Nat ∷ (λ (n ∷ []) → Fin n) (Nat ∷ [])  ∷ []) → Set

tylist = A ∷   <-- toHetList [] → Set
         B ∷   <-- toHetList (A ∷ []) → Set
         C ∷   <-- toHetList (A ∷ B ∷ []) → Set
-}



------------------------------
-- The FepList class of datatypes can have a different B function for every
-- element. This function must come from a separate list??

-- data FepList {a b}{A : Set a}(B : A → Set b)(f : (acc : A) → B acc → A) : A → Set (a ⊔ b) where
--   [] : ∀{acc} → FepList B f acc
--   _∷_ : ∀{acc} → (x : B acc) → (xs : FepList B f (f acc x)) → FepList B f acc

-- Env : {!!} --List Set → Set
-- Env = DepList {A = List Set} (λ XS → HetList XS → Set) (λ acc x → {!!} ∷ acc)





  -- data Env : Set₁ where
  --   _then_ : (t : Env)(f : UseEnv t → Set) → Env
  --   start : Set → Env
  -- UseEnv : Env → Set
  -- UseEnv (t then f) = Σ (UseEnv t) f
  -- UseEnv (start v) = v





-- {-
-- Wat weten we at definition-time?
-- De types van dingen, maar niet de waardes. Dus bij wrapEq weten we dat:
-- - A : Set, maar niet de waarde van A?
-- - x en y : A, maar niet de waardes van x en y
-- Bij blob gebruiken we (Fin : Nat → Set) om een type te maken
-- - n : Nat, maar niet d
-- Dus de environment moet alleen de types van dingen opslaan.
-- -}

data EnvTy : Set₁ where
  ty-x : (X : Set) → EnvTy
  ty-set : EnvTy
data EnvVal : EnvTy → Set₁ where
  val-x : {X : Set}(v : X) → EnvVal (ty-x X)
  val-set : (v : Set) → EnvVal ty-set
envVal-to-envTy : ∀{et} → EnvVal et → Maybe EnvTy
envVal-to-envTy (val-x v) = nothing
envVal-to-envTy (val-set v) = just (ty-x v)

envFin : EnvVal (ty-x Nat) → EnvVal ty-set
envFin (val-x v) = val-set (Fin v)

-- Env : Set₁
-- Env = List EnvTy
-- emptyEnv : Env
-- emptyEnv = []
-- -- envVals : Env → List (Σ EnvTy EnvVal)
-- -- envVals E = map {!!} E
-- envFunc : Env → Set₂
-- envFunc ets = ({!map!}) → Set

infixl 4 _▷_
mutual
  data Cx : Set₁ where
    _▷_ : (Γ : Cx)(f : ⟦ Γ ⟧C → Set) → Cx
    ε : Cx
  ⟦_⟧C : Cx → Set
  ⟦ Γ ▷ f ⟧C = Σ ⟦ Γ ⟧C f
  ⟦ ε ⟧C = ⊤

infix 3 _∋_
data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧C → Set) → Set where
  top : ∀{Γ T} → Γ ▷ T ∋ T ∘ fst
  pop : ∀{Γ S T} → Γ ∋ T → Γ ▷ S ∋ T ∘ fst

⟦_⟧∋ : ∀{Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → T γ
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

ex-cx : Cx
ex-cx = ε
      ▷ (λ { tt → Nat })
      ▷ (λ { (tt , n) → Fin n })
      ▷ (λ { ((tt , n) , k) → Bool })

infixr 3 _`+_
infixr 4 _`*_
data ConDesc : Cx → Set₁ where
  ι : ∀{Γ} → ConDesc Γ
  _`*_ : ∀{Γ}(S : ⟦ Γ ⟧C → Set) → (xs : ConDesc (Γ ▷ S)) → ConDesc Γ
  rec-*_ : ∀{Γ}(xs : ConDesc Γ) → ConDesc Γ
data DatDesc : Nat → Set₁ where
  `0 : DatDesc 0
  _`+_ : ∀{#c}(x : ConDesc ε)(xs : DatDesc #c) → DatDesc (suc #c)

t : DatDesc 1
-- t = const Nat `* const Bool `* (λ γ → Fin (⟦ pop top ⟧∋ γ)) `* ι `+ `0
t = const Nat `* const Bool `* (λ γ → Fin (snd (fst γ))) `* ι `+ `0
-- t = const Nat `* const Bool `* (λ { ((tt , n) , b) → Fin n }) `* ι `+ `0

⟦_⟧conDesc : ∀{Γ} → ConDesc Γ → ⟦ Γ ⟧C → Set → Set
⟦ ι ⟧conDesc γ X = ⊤
⟦ S `* xs ⟧conDesc γ X = Σ (S γ) λ s → ⟦ xs ⟧conDesc (γ , s) X
⟦ rec-* xs ⟧conDesc γ X = X × ⟦ xs ⟧conDesc γ X

