module IR where

open import Common
open import Builtin.Size

Slice : Set → Set₁
Slice I = Σ Set (λ X → X → I)

ISet : Set → Set₁
ISet I = (i : I) → Set

_→↑_ : ∀ {I} → (r s : ISet I) → Set
r →↑ s = ∀ i → r i → s i

Slice→ISet : ∀{I} → Slice I → ISet I
Slice→ISet (X , f) i = Σ X (λ x → f x ≡ i)

ISet→Slice : ∀{I} → ISet I → Slice I
ISet→Slice F = (Σ _ F) , fst

module SmallInductionRecursion-SumProd where
  data IR (I O : Set) : Set₁ where
    ι : (o : O) → IR I O
    σ : (S : Set) (K : S → IR I O) → IR I O
    δ : (P : Set) (K : (P → I) → IR I O) → IR I O

  module DS where
    SlSg : {I : Set}(S : Set)(T : S → Slice I) → Slice I
    SlSg S T = Σ S (fst ∘ T) , λ { (s , t) → snd (T s) t }

    ⟦_⟧DS : ∀{I O} → IR I O → Slice I → Slice O
    ⟦ ι o ⟧DS (X , f) = ⊤ , (λ _ → o)
    ⟦ σ S K ⟧DS (X , f) = SlSg S (λ s → ⟦ K s ⟧DS (X , f))
    ⟦ δ P K ⟧DS (X , f) = SlSg (P → X) (λ x → ⟦ K (f ∘ x) ⟧DS (X , f))

    -- mutual
    --   data μ {I : Set} (γ : IR I I) : Set where
    --     ⟨_⟩ : fst (⟦ γ ⟧DS (μ γ , decode γ)) → μ γ
    --   decode : ∀{I} → (γ : IR I I) → μ γ → I
    --   decode γ ⟨ t ⟩ = snd (⟦ γ ⟧DS (μ γ , decode γ)) t

  module IR- where
    ⟦_⟧IR : ∀ {I O} → IR I O → (I → Set) → (O → Set)
    ⟦ ι o′ ⟧IR F o = o′ ≡ o
    ⟦ σ S K ⟧IR F o = Σ S (λ s → ⟦ K s ⟧IR F o)
    ⟦ δ P K ⟧IR F o = Σ (P → Σ _ F) (λ if → ⟦ K (fst ∘ if) ⟧IR F o)

    data μ {I : Set} (F : IR I I)
           (r : ISet I) (o : I) : Set where
      ⟨_⟩ : ⟦ F ⟧IR r o → μ F r o

    -- mutual
    --   data μ {I : Set} (γ : IR I I) : Set where
    --     ⟨_⟩ : fst (⟦ γ ⟧IR (μ γ , decode γ)) → μ γ
    --     ⟨_⟩ : ⟦ γ ⟧IR (μ γ , decode γ) → μ γ
      -- decode : ∀{I} → (γ : IR I I) → μ γ → I
      -- decode γ t = {!⟦ γ ⟧IR )!} --snd (⟦ γ ⟧IR (μ γ , decode γ)) t

  module Mix where
    ⟦_⟧set : ∀{I O} (C : IR I O) (X : Set) (f : X → I) → Set
    ⟦ ι o ⟧set X f = ⊤
    ⟦ σ S K ⟧set X f = Σ S (λ s → ⟦ K s ⟧set X f)
    ⟦ δ P K ⟧set X f = Σ (P → X) (λ x → ⟦ K (f ∘ x) ⟧set X f)
    ⟦_⟧out : ∀{I O} (C : IR I O) (X : Set) (f : X → I) → ⟦ C ⟧set X f → O
    ⟦ ι o ⟧out X f tt = o
    ⟦ σ S K ⟧out X f (s , t) = ⟦ K s ⟧out X f t
    ⟦ δ P K ⟧out X f (x , t) = ⟦ K (f ∘ x) ⟧out X f t

    mutual
      data μ {I : Set} (γ : IR I I) {sz : Size} : Set where
        ⟨_⟩ : {sz′ : Size< sz} → ⟦ γ ⟧set (μ γ {sz′}) (decode γ) → μ γ
      decode : ∀{I sz} → (γ : IR I I) → μ γ {sz} → I
      decode γ ⟨ t ⟩ = ⟦ γ ⟧out (μ γ) (decode γ) t
 
  sum' prod' : (n : Nat) → (Fin n → Nat) → Nat
  sum' zero f = 0
  sum' (suc n) f = (f zero) + (sum' n (f ∘ suc))
  prod' zero f = 1
  prod' (suc n) f = (f zero) * (prod' n (f ∘ suc))

  data Tag : Set where fin′ sum′ prod′ : Tag

  lang : IR Nat Nat
  lang = σ Tag λ { fin′ → σ Nat λ n → ι n
                 ; sum′ → δ ⊤ λ n → δ (Fin (n tt)) λ f → ι (sum' (n tt) f)
                 ; prod′ → δ ⊤ λ n → δ (Fin (n tt)) λ f → ι (prod' (n tt) f)
                 }

  example : Mix.μ lang
  example = ⟨ sum′ , (λ _ → ⟨ fin′ , 5 , tt ⟩) , (λ n → ⟨ fin′ , finToNat n , tt ⟩) , tt ⟩
    where open Mix
  -- Mix.decode lang example == 10

  -- example2 : IR-.μ lang
  -- example2 = ?
  --   where open IR-

  natD : IR ⊤ ⊤
  natD = σ Bool λ { false → δ ⊤ (λ x → ι tt)
                  ; true → ι tt
                  }

  nat-ex : Mix.μ natD
  nat-ex = Mix.⟨ false , (λ _ → Mix.⟨ true , tt ⟩) , tt ⟩

  finD : IR {!!} {!!}
  finD = σ Bool λ { false → ι {!!}
                  ; true → δ ⊤ (λ X → ι {!X tt !})
                  }

  flem : {!Mix.⟦ natD ⟧set!}
  flem = {!Mix.decode natD nat-ex!}


module TuringCompletenessTotallyFree where
  data IR {S : Set} (I : S → Set) (O : Set) : Set₁ where
    ι : (o : O) → IR I O
    σ : (A : Set) (K : A → IR I O) → IR I O
    δ : (B : Set) (s : B → S)
        (K : (i : (b : B) → I (s b)) → IR I O) → IR I O
  
  ⟦_⟧set : ∀ {S I O} (C : IR I O) (X : S → Set) (i : X →↑ I) → Set
  ⟦ ι o ⟧set X i = ⊤
  ⟦ σ A K ⟧set X i = Σ A (λ a → ⟦ K a ⟧set X i)
  ⟦ δ B s K ⟧set X i = Σ ((b : B) → X (s b)) (λ r → ⟦ (K (i _ ∘ r)) ⟧set X i)

  ⟦_⟧out : ∀ {S I O} (C : IR I O) (X : S → Set) (i : X →↑ I) →
           ⟦ C ⟧set X i → O
  ⟦ ι o ⟧out X i tt = o
  ⟦ σ A K ⟧out X i (a , t) = ⟦ K a ⟧out X i t
  ⟦ δ B s K ⟧out X i (r , t) = ⟦ K (i _ ∘ r) ⟧out X i t

  mutual
    data μ {S I} (F : (s : S) → IR I (I s)) (j : Size) (s : S) : Set where
      ⟨_⟩ : {k : Size< j} → ⟦ F s ⟧set (μ F k) decode → μ F j s
    decode : ∀ {S I F j} → μ {S} {I} F j →↑ I
    decode {F = F} i ⟨ n ⟩ = ⟦ F i ⟧out (μ F _) decode n

  -- ⟦_⟧set and ⟦_⟧out together give us a slice. The input also turns out to be a slice.

  la : {S : Set}{I : S → Set} → Iso (Σ ((s : S) → Set) (λ X → X →↑ I))
                                    ((s : S) → Slice (I s))
  la = record
    { to = λ { (l , r) s → l s , r s }
    ; from = λ x → (λ s → fst (x s)) , (λ s → snd (x s))
    ; to-from = λ x → {!!}
    ; from-to = λ x → {!!}
    }

  ⟦_⟧slice : ∀ {S I O} (C : IR I O) → ((s : S) → Slice (I s)) → Slice O
  -- ⟦ C ⟧slice X i = ⟦ C ⟧set X i , ⟦ C ⟧out X i
  ⟦_⟧slice C a with Iso.from la a
  ... | X , i = ⟦ C ⟧set X i , ⟦ C ⟧out X i

  ⟦_⟧slice⊤ : ∀ {I O} (C : IR {⊤} (const I) O) → Slice I → Slice O
  ⟦_⟧slice⊤ C a = ⟦ C ⟧slice (const a)

  natD : IR ⊥-elim ⊤
  natD = σ (Fin 2) (λ { zero → ι tt
                      ; (suc zero) → δ ⊥ id (λ i → {!!})
                      ; (suc (suc ()))
                      })

