

-- PREVIOUS VERSION 3bf603f


-- Ornaments on the descriptions of DescDT

module DatatypeDescriptions.SingleOrnament where

open import Prelude
open import Shared.Semantics
import DatatypeDescriptions.Desc as Desc

open Desc.Single

{-

Deze ornaments zijn grotendeels vergelijkbaar met die van 'transporting
functions across ornaments', maar doordat wij andere descriptions gebruiken zijn
er iets andere mogelijkheden.
Naast de copy-constructors bevatten hun ornaments constructors om de var te
kopieren met een refined index.
De insert-rec en recons zijn dubieus, omdat ze de structuur (arities) kunnen
veranderen. give-K is denk ik ok want de structuur wordt niet veranderd.
ι, ΣK : copy-constructors
rec*_ : copy-constructor. Als we indices hebben kan deze ook de index refinen,
        net als in tfao.
insert-K : Voeg een ΣK in, de rest van de ornament kan de waarde hiervan
           gebruiken. Zelfde als insert in tfao
insert-rec : Voeg een recursieve call in. Deze zit niet in tfao omdat hun
             descriptions geen rec aan de linkerkant van een * toestaan. Daar
             kan een rec enkel aan een eind (als leaf) van een type worden
             geplaatst. 
give-K : Zelfde als delete in tfao. Door een waarde voor de K in te vullen kan
         de K veilig verwijderd worden, en nog teruggehaald worden in de forget.
`0, _`+_ : copy-constructors
recons : De constructorspine (c₁ `+ c₂ `+ .. `+ cn) wordt geinterpreteerd als
         een ΣK (Fin n) .. . In tfao wordt dit effect bereikt door een
         ΣK (Fin n) .. te gebruiken, waar je dus ook een give-K op kan doen.
         Daarmee kies je eigenlijk een enkele constructor van het datatype.
         Hoewel onze constructorspine semantisch vergelijkbaar is met een ΣK
         op het top-level, kunnen we deze niet zonder meer deleten want dan is
         hebben we geen DatDesc meer (een DatDesc ornament moet een DatDesc
         opleveren). Ook kan deze constructorspine niet geinsert worden dmv een
         ornament, want dan zou je daarvoor een datatype zonder constructorspine
         moeten hebben.
         In tfao zijn een aantal voorbeelden waarbij er wel een top-level ΣK
         geinsert wordt, en daarbij wordt voor elke positie een give gedaan om
         een constructor uit het eerste datatype te kiezen. Dit gedrag kunnen
         we wel afvangen door deze insert en deletes op het top-level te
         combineren tot onze recons.
         De informatie die door de gebruiker gegeven moet worden is een
         combinatie van die voor insert-ΣK en give-K. De insert-ΣK heeft twee
         argumenten (S : Set) en (f : (s : S) → Orn (xs s)). Omdat we een
         constructorspine willen maken gebruiken we niet een arbitraire S als
         key maar maar een Fin n, waarbij n het aantal constructors van het
         outputtype is en door de gebruiker gegeven wordt. Met het oude type van
         de functie f kon de gebruiker voor elke positie een ornament geven.
         Nu willen we eigenlijk afdwingen dat er als eerste een give wordt
         gedaan. De benodigde gegevens om dat te doen kunnen we zien in het type
         van give-K, een (s : S) en een (xs⁺ : Orn (xs s)). Omdat de give op een
         constructorspine wordt gedaan is deze S altijd een Fin #c, waarbij #c
         hier juist het aantal constructors van het inputtype is. Het
         resulterende type zorgt ervoor dat de gebruiker het nieuwe aantal
         constructors kan kiezen, en voor elke nieuwe constructor kan kiezen
         met welke oude constructor het overeen komt.
         Voorbeeld usecase: Je hebt List A, en wil een ABList A B maken die twee
         soorten nodes heeft.

-}
mutual
  ConOrn : ConDesc → Set₁
  ConOrn = Orn
  DatOrn : ∀{#c} → DatDesc {#c} → Set₁
  DatOrn = Orn

  data Orn : ∀{dt} (D : Desc dt) → Set₁ where
    ι : ConOrn ι
    ΣK : ∀{S xs} → (xs⁺ : (s : S) → Orn (xs s)) → ConOrn (ΣK S xs)
    rec-*_ : ∀{xs} → (xs⁺ : Orn xs) → ConOrn (rec-* xs)

    insert-ΣK : ∀{xs} → (S : Set) → (xs⁺ : S → Orn xs) → ConOrn xs
    insert-rec : ∀{xs} → (xs⁺ : Orn xs) → ConOrn xs
    give-K : ∀{S xs} → (s : S) → (xs⁺ : Orn (xs s)) → ConOrn (ΣK S xs)

    `0 : DatOrn `0
    _`+_ : ∀{#c x xs} → (x⁺ : Orn x) (xs⁺ : Orn xs) → DatOrn {suc #c} (x `+ xs)

    recons : ∀ #c⁺ {#c} {D : DatDesc {#c}} →
             (f : (k⁺ : Fin #c⁺) → (Σ (Fin #c) λ k → Orn (lookupCtor D k))) → DatOrn {#c} D

insert-K_*_ : ∀{xs} → (S : Set) → (xs⁺ : Orn xs) → ConOrn xs
insert-K S * xs⁺ = insert-ΣK S (const xs⁺)

simple-recons : ∀ #c {D : DatDesc {#c}} →
                (f : (k : Fin #c) → Orn (lookupCtor D k)) → DatOrn {#c} D
simple-recons #c f = recons #c (λ k → k , f k)


----------------------------------------
-- Semantics

tabulateCtors : ∀{n} → (Fin n → ConDesc) → DatDesc {n}
tabulateCtors {zero} f = `0
tabulateCtors {suc n} f = f 0 `+ tabulateCtors (f ∘ suc)

private
  conOrnToDesc : {D : ConDesc} → Orn D → ConDesc
  conOrnToDesc ι = ι
  conOrnToDesc (ΣK xs⁺) = ΣK _ λ s → conOrnToDesc (xs⁺ s)
  conOrnToDesc (rec-* o) = rec-* (conOrnToDesc o)
  conOrnToDesc (insert-ΣK S xs⁺) = ΣK S λ s → conOrnToDesc (xs⁺ s)
  conOrnToDesc (insert-rec xs⁺) = rec-* (conOrnToDesc xs⁺)
  conOrnToDesc (give-K s xs⁺) = conOrnToDesc xs⁺
  ornToDesc-#c : ∀{#c}{D : DatDesc {#c}} → Orn D → Nat
  ornToDesc-#c `0 = 0
  ornToDesc-#c (_ `+ xs⁺) = suc (ornToDesc-#c xs⁺)
  ornToDesc-#c (recons n _) = n
  ornToDesc-dt : ∀{dt}{D : Desc dt} → Orn D → DescTag
  ornToDesc-dt {`ctag} _ = `ctag
  ornToDesc-dt {`dtag _} o = `dtag (ornToDesc-#c o)
ornToDesc : ∀{dt}{D : Desc dt}(o : Orn D) → Desc (ornToDesc-dt o)
ornToDesc {`ctag} o = conOrnToDesc o
ornToDesc {`dtag _} `0 = `0
ornToDesc {`dtag _} (x⁺ `+ xs⁺) = conOrnToDesc x⁺ `+ ornToDesc xs⁺
ornToDesc {`dtag _} (recons _ xs⁺) = tabulateCtors (conOrnToDesc ∘ snd ∘ xs⁺)
{-# DISPLAY conOrnToDesc = ornToDesc #-}

instance orn-semantics : ∀{dt}{D : Desc dt} → Semantics (Orn D)
         orn-semantics = record { ⟦_⟧ = ⟦_⟧ ∘ ornToDesc }

----------------------------------------
-- Ornamental algebra

lookup-tabulate : ∀{#c}(f : Fin #c → ConDesc) i →
                  lookupCtor (tabulateCtors f) i ≡ f i
lookup-tabulate f zero = refl
lookup-tabulate f (suc i) = lookup-tabulate (f ∘ suc) i

private
  conForgetNT : {D : ConDesc} (o : Orn D) → ∀ X → ⟦ o ⟧ X → ⟦ D ⟧ X
  conForgetNT ι X tt = tt
  conForgetNT (ΣK xs⁺) X (s , v) = s , conForgetNT (xs⁺ s) X v
  conForgetNT (rec-* xs⁺) X (s , v) = s , conForgetNT xs⁺ X v
  conForgetNT (insert-ΣK S xs⁺) X (s , v) = conForgetNT (xs⁺ s) X v
  conForgetNT (insert-rec xs⁺) X (s , v) = conForgetNT xs⁺ X v
  conForgetNT (give-K s xs⁺) X v = s , conForgetNT xs⁺ X v
forgetNT : ∀{dt}{D : Desc dt} (o : Orn D) → ∀ X → ⟦ o ⟧ X → ⟦ D ⟧ X
forgetNT {`ctag} = conForgetNT
forgetNT {`dtag _} `0 X (() , _)
forgetNT {`dtag _} (x⁺ `+ xs⁺) X (zero , v) = zero , conForgetNT x⁺ X v
forgetNT {`dtag _} (x⁺ `+ xs⁺) X (suc k , v) = (suc *** id) (forgetNT xs⁺ X (k , v))
forgetNT {`dtag _} (recons _ f) X (c , v) =
  let v′ = transport (λ a → ⟦_⟧ a X) (lookup-tabulate _ c) v in
  fst (f c) , conForgetNT (snd (f c)) X v′

forgetAlg : ∀{#c}{D : DatDesc {#c}} (o : Orn D) → Alg (ornToDesc o) (μ D)
forgetAlg o = ⟨_⟩ ∘ forgetNT o _

forget : ∀{#c}{D : DatDesc {#c}} → (o : Orn D) → μ (ornToDesc o) → μ D
forget o x = fold (forgetAlg o) x

orn-id : ∀{dt}{D : Desc dt} → Orn D
orn-id {D = ι} = ι
orn-id {D = ΣK S xs} = ΣK λ s → orn-id
orn-id {D = rec-* xs} = rec-* orn-id
orn-id {D = `0} = `0
orn-id {D = x `+ xs} = orn-id `+ orn-id

nat→natlist : Orn natD
nat→natlist = ι `+ insert-K Nat * (rec-* ι) `+ `0

barD : DatDesc
barD = K (Either Nat Bool) * ι `+ `0
bar→barb : Orn barD
bar→barb = recons 2 λ { zero → 0 , insert-ΣK Nat (λ s → give-K (left s) ι)
                      ; (suc zero) → 0 , insert-ΣK Bool (λ s → give-K (right s) ι)
                      ; (suc (suc ()))
                      }
test-barb : ornToDesc bar→barb ≡ (K Nat * ι `+ K Bool * ι `+ `0)
test-barb = refl
ex-forget-bar→barb : forget bar→barb ⟨ 1 , true , tt ⟩ ≡ ⟨ 0 , right true , tt ⟩
ex-forget-bar→barb = refl

-- botD : Desc
-- botD = `0

-- bot→unit : Orn botD
-- bot→unit = insert-con ι `0

-- -- bot→pair : Orn botD
-- -- bot→pair =  -- composition would be nice

-- unit→nat : Orn ⟦ bot→unit ⟧
-- -- unit→nat = conOrn-id `+ insert-con (rec-* ι) `0
-- unit→nat = insertConstructor 1 (rec-* ι)

nat→list : Orn natD
nat→list = simple-recons 2 (λ { zero → ι; (suc zero) → insert-K Nat * rec-* ι ; (suc (suc ())) })

module Plus-redundant where
  tabulate-lookup : ∀{#c}(xs : DatDesc {#c}) →
                    tabulateCtors (lookupCtor xs) ≡ xs
  tabulate-lookup `0 = refl
  tabulate-lookup (x `+ xs) = cong (_`+_ x) (tabulate-lookup xs)

  tabulate-lookup-ext : ∀{#c}(xs : DatDesc {#c}) →
                        {f : (x : Fin #c) → ConDesc} → (∀ k → f k ≡ lookupCtor xs k) →
                        tabulateCtors f ≡ xs
  tabulate-lookup-ext `0 eq = refl
  tabulate-lookup-ext (x `+ xs) eq = cong₂ _`+_ (eq 0) (tabulate-lookup-ext xs (eq ∘ suc))

  `0-redundant : ornToDesc {D = `0} `0 ≡ ornToDesc {D = `0} (recons 0 (λ { () }))
  `0-redundant = refl

  forget-ctorChoice : ∀{#c}{D : DatDesc {#c}} (o : Orn D) → Fin (ornToDesc-#c o) → Fin #c
  forget-ctorChoice `0 ()
  forget-ctorChoice (x⁺ `+ xs⁺) zero = zero
  forget-ctorChoice (x⁺ `+ xs⁺) (suc k) = suc (forget-ctorChoice xs⁺ k)
  forget-ctorChoice (recons n f) k = fst (f k)

  orn-lookupCtor : ∀{#c}{xs : DatDesc {#c}}(xs⁺ : Orn xs) k → Orn (lookupCtor xs (forget-ctorChoice xs⁺ k))
  orn-lookupCtor `0 ()
  orn-lookupCtor (x⁺ `+ xs⁺) zero = x⁺
  orn-lookupCtor (x⁺ `+ xs⁺) (suc k) = orn-lookupCtor xs⁺ k
  orn-lookupCtor (recons n f) k = snd (f k)

  ornToDesc-lookup : ∀{#c}{xs : DatDesc {#c}}(xs⁺ : Orn xs) k → ornToDesc (orn-lookupCtor xs⁺ k) ≡ lookupCtor (ornToDesc xs⁺) k
  ornToDesc-lookup `0 ()
  ornToDesc-lookup (x⁺ `+ xs⁺) zero = refl
  ornToDesc-lookup (x⁺ `+ xs⁺) (suc k) = ornToDesc-lookup xs⁺ k
  ornToDesc-lookup (recons n f) k = sym (lookup-tabulate (ornToDesc ∘ snd ∘ f) k)

  `+-by-recons : ∀{#c x xs} → (x⁺ : Orn x) (xs⁺ : Orn xs) → DatOrn {suc #c} (x `+ xs)
  `+-by-recons x⁺ xs⁺ = recons (suc (ornToDesc-#c xs⁺)) λ
                        { zero → 0 , x⁺
                        ; (suc k) → suc (forget-ctorChoice xs⁺ k) , orn-lookupCtor xs⁺ k
                        }

  `+-redundant : {n : Nat}{A : ConDesc}{B : DatDesc {n}}(A⁺ : Orn A)(B⁺ : Orn B) →
                 ornToDesc {D = A `+ B} (`+-by-recons A⁺ B⁺) ≡
                 ornToDesc {D = A `+ B} (A⁺ `+ B⁺)
  `+-redundant A⁺ B⁺ = cong (_`+_ (ornToDesc A⁺))
                            (tabulate-lookup-ext (ornToDesc B⁺) (ornToDesc-lookup B⁺))
