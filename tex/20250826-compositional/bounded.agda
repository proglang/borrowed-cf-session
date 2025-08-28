module bounded where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _⊔_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; _∪_; ⊥; _⊆_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (nonempty?; _∈?_; ∪-idem)
open import Data.Product as Product using (∃; ∄; _×_; _,_; proj₁)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; subst; _≢_; sym)

-- aux
m⊔n≤o⇒m≤o : ∀ m n o → m ⊔ n ≤ o → m ≤ o
m⊔n≤o⇒m≤o zero n o z≤n = z≤n
m⊔n≤o⇒m≤o zero n o (s≤s m⊔n≤o) = z≤n
m⊔n≤o⇒m≤o (suc m) zero o m⊔n≤o = m⊔n≤o
m⊔n≤o⇒m≤o (suc m) (suc n) (suc o) (s≤s m⊔n≤o) = s≤s (m⊔n≤o⇒m≤o m n o m⊔n≤o)

m⊔n≤o⇒n≤o : ∀ m n o → m ⊔ n ≤ o → n ≤ o
m⊔n≤o⇒n≤o m zero o m⊔n≤o = z≤n
m⊔n≤o⇒n≤o zero (suc n) o m⊔n≤o = m⊔n≤o
m⊔n≤o⇒n≤o (suc m) (suc n) zero ()
m⊔n≤o⇒n≤o (suc m) (suc n) (suc o) (s≤s m⊔n≤o) = s≤s (m⊔n≤o⇒n≤o m n o m⊔n≤o)

1+m≤o⇒m≤o : ∀ m o → suc m ≤ o → m ≤ o
1+m≤o⇒m≤o m (suc o) (s≤s 1+m≤o) = ≤-trans 1+m≤o (n≤1+n o)

variable
  n k : ℕ

-- k - variables
-- n - size of alphabet

data Session (n : ℕ) : (k : ℕ) → Set where
  `_   : Fin k → Session n k
  Skip : Session n k
  Atom : Fin n → Session n k
  Seq  : Session n k → Session n k → Session n k
  Choice : Session n k → Session n k → Session n k
  Mu   : Session n (suc k) → Session n k


  
{-
-- Lang is a complete lattice (set of languages) ordered by ⊆

L : Session → LEnv → Lang
L X η = η X
L ε η = { ε }
L A η = { A }
L (S₁ ; S₂) η = L S₁ η · L S₂ η
L (S₁ & S₂) η = inl $ L S₁ η ∪ inr $ L S₂ η
L (μX.S) η = fix λA → L S η[ X ↦ A ]
-}

-- need to talk about subsets of Σ≤1, the set of words of length ≤ 1
-- let W≤1 be a type representing a set of words of length ≤ 1
-- could be represented by type `Subset (suc n)` where
-- 0 - the empty word
-- i - symbol #i, for 1 ≤ i ≤ n

Sym : ℕ → Set
Sym n = Fin (2 + n)

WSet : ℕ → Set
WSet n = Subset (2 + n)

weps : Sym n
weps = zero

-- concatenation of last symbols
conc : Sym n → Sym n → Sym n
conc zero y = y
conc (suc x) zero = suc x
conc (suc x) (suc y) = suc y

-- concW : WSet n → WSet n → WSet n
-- concW x y = { conc a? b? ∣ a? ∈ x, b? ∈ y }

concW : WSet n → WSet n → WSet n
concW X Y
  with nonempty? X
... | no ¬a = ⊥
... | yes a
  with nonempty? Y
... | no ¬b = ⊥
... | yes b
  with weps ∈? Y
... | no zero∉ = Y
... | yes zero∈ = X ∪ Y

concSW : Sym n → WSet n → WSet n
concSW zero Y = Y
concSW (suc x) Y
  with nonempty? Y
... | no ¬a = ⊥
... | yes a
  with weps ∈? Y
... | no weps∉ = Y
... | yes weps∈ = ⁅ suc x ⁆ ∪ Y

-- a pointed CPO (actually a complete lattice)
_⊑_ : WSet n → WSet n → Set
a? ⊑ b? = a? ⊆ b?

-- -- language of last symbols of finite words
-- L$ : Session → SymEnv → Maybe (Maybe Sym)
-- L$ X η = η X
-- L$ ε η = { ε }
-- L$ a η = { a }
-- L$ (S₁ ; S₂) η = conc≤1 (L$ S₁ η) (L$ S₂ η)
-- L$ (S₁ & S₂) η = map (conc inl) (L$ S₁ η) ∪ map (conc inr) (L$ S₂ η)
-- L$ (μX.S) η = fix λ A → L$ S η[ X ↦ A ]

postulate
  fix : ∀ {A : Set} → (A → A) → A

ext : ∀ {A : Set} → (Fin k → A) → A → (Fin (suc k) → A)
ext η a zero = a
ext η a (suc i) = η i

L$ : Session n k → (Fin k → WSet n) → WSet n
L$ (` x) η = η x
L$ Skip η = ⁅ weps ⁆
L$ (Atom x) η = ⁅ suc (suc x) ⁆
L$ (Seq S S₁) η = concW (L$ S η) (L$ S₁ η)
L$ (Choice S S₁) η = concSW (suc zero) (L$ S η) ∪ concSW (suc zero) (L$ S₁ η)
L$ (Mu S) η = fix (λ A → L$ S (ext η A))

-- version with step count

fix′ : (WSet n → ℕ → WSet n) → ℕ → WSet n
fix′ f zero = ⊥
fix′ f (suc i) = f (fix′ f i) i


L$′ : Session n k → (Fin k → WSet n) → ℕ → WSet n
L$′ (` x) η i = η x
L$′ Skip η i = ⁅ weps ⁆
L$′ (Atom x) η i = ⁅ suc (suc x) ⁆
L$′ (Seq S S₁) η i = concW (L$′ S η i) (L$′ S₁ η i)
L$′ (Choice S S₁) η i = concSW (suc zero) (L$′ S η i) ∪ concSW (suc zero) (L$′ S₁ η i)
L$′ (Mu S) η i = fix′ (λ A → L$′ S (ext η A)) i

variable
  S S₁ S₂ : Session n k

-- session types generating the empty trace

data skips : Session n k → Set where

  skips-Skip : skips {n} {k} Skip

  skips-Seq  : skips S₁ → skips S₂ → skips (Seq S₁ S₂)

  skips-Mu   : skips S → skips (Mu S)

module foo where

  sound-skips-fix : {S : Session n (suc k)} (η : Fin k → WSet n) → skips S
    → ∃ λ j → ∀ i → j ≤ i → fix′ (λ A → L$′ S (ext η A)) i ≡ ⁅ weps ⁆

  sound-skips : {S : Session n k} (η : Fin k → WSet n) → skips S
    → ∃ λ j → ∀ i → j ≤ i → L$′ S η i ≡ ⁅ weps ⁆

  sound-skips-fix {S = S} η sk
    with sound-skips (ext η ⊥) sk
  ... | j , iv = suc j , aux
    where
      aux : (i : ℕ) → suc j ≤ i → fix′ (λ A → L$′ S (ext η A)) i ≡ ⁅ weps ⁆
      aux i 1+j≤i = {!iv i (1+m≤o⇒m≤o j i 1+j≤i)!}

  sound-skips η skips-Skip = 0 , (λ i x → refl)
  sound-skips {S = Seq S₁ S₂} η (skips-Seq sk sk₁)
    with sound-skips η sk | sound-skips η sk₁
  ... | j , iv | j₁ , iv₁ = (j ⊔ j₁) , aux
    where
      aux : (i : ℕ) → j ⊔ j₁ ≤ i → concW (L$′ S₁ η i) (L$′ S₂ η i) ≡ ⁅ weps ⁆
      aux i x
        rewrite iv i (m⊔n≤o⇒m≤o j j₁ i x)
        rewrite iv₁ i (m⊔n≤o⇒n≤o j j₁ i x)
          = ∪-idem ⁅ weps ⁆
    
  sound-skips η (skips-Mu sk) = sound-skips-fix η sk

sound-skips-fix : (S : Session n (suc k)) (η : Fin k → WSet n) → skips S
  → ∀ i → fix′ (λ A → L$′ S (ext η A)) i ≡ ⁅ weps ⁆
sound-skips : (S : Session n k) (η : Fin k → WSet n) → skips S
  → ∀ i → L$′ S η i ≡ ⁅ weps ⁆

sound-skips (` x) η () i
sound-skips Skip η skips-Skip i = refl
sound-skips (Atom x) η () i
sound-skips (Seq S S₁) η (skips-Seq sk sk₁) i
  with sound-skips S η sk i | sound-skips S₁ η sk₁ i
... | iv | iv₁
  rewrite iv | iv₁ = ∪-idem ⁅ weps ⁆
sound-skips (Choice S S₁) η () i
sound-skips (Mu S) η (skips-Mu sk) i = sound-skips-fix S η sk i

sound-skips-fix S η sk zero = {!!}
sound-skips-fix S η sk (suc i) = {!!}

-- -- session types generating at least one finite trace

-- data finite : Session → Set where

--   finite ε

--   finite a

--   finite S₁ → finite S₂ → finite (S₁ ; S₂)

--   finite S₁ → finite (S₁ & S₂)

--   finite S₂ → finite (S₁ & S₂)

--   finite S → finite (μX.S)

-- fn : ∀ S → (fn : finite S)
--          → L$ S η ⊃ ∅
-- fn X = OK: ¬ finite
-- fn ε = OK:
-- fn a = OK:
-- fn (S₁ ; S₂) = OK: by IVs
-- fn (S₁ & S₂) = OK: by IVs
-- fn (μX.S) = fixed point induction
--   base case: fn S η[ X ↦ ∅ ] ok by outer IV
--   inductive case: if A ⊃ ∅ then fn S η[ X ↦ A ] ⊃ ∅ by outer IV

-- -- session types generating only infinite traces

-- data loops : Session → Set where

--   loops X

--   loops S₁ → loops (S₁ ; S₂)

--   finite S₁ → loops S₂ → loops (S₁ ; S₂)

--   loops S₁ → loops S₂ → loops (S₁ & S₂)

--   loops S → loops (μX.S)

-- lp : ∀ S → (ass-X : ∀ X ∈ dom η → η X = ∅) (lps : loops S) → L$ S η = ∅
-- lp X = OK: by ass-X
-- lp ε = OK: ¬ loops ε
-- lp a = OK: ¬ loops a
-- lp (S₁ ; S₂) = cases by inversion on lps
--   1. loops S₁ : by iv, L$ S₁ η = ∅, hence conc≤1 (L$ S₁ η) (L$ S₂ η) = ∅
--   2. finite S₁, loops S₂ : by iv, L$ S₂ η = ∅, hence ... = ∅
-- lp (S₁ & S₂) = immediate by ivs
-- lp (μX.S) = by fixed point induction
--   base case: L$ S η[ X ↦ ∅ ] = ∅ by outer iv
--   ind. case: same

-- -- bounded session types

-- data bounded : Session → Set where

--   bounded X

--   bounded □

--   finite S₁ → bounded S₂ → bounded (S₁ ; S₂)

--   loops S₁ → bounded (S₁ ; S₂)

--   bounded S₁ → bounded S₂ → bounded (S₁ & S₂)

--   bounded S → bounded (μX.S)

-- -- the lemma
-- rb : ∀ S → (dom-η : dom η ⊆ var S)
--          → (ass-X : ∀ X ∈ dom η → η X ⊆ { □ })
--          → (bs : bounded S)
--          → L$ S η ⊆ { □ }
-- rb X = OK: ass-X X
-- rb ε = OK: ¬ bounded ε
-- rb a = OK: bounded a → a ≡ □
-- rb (S₁ ; S₂) = cases by inversion on bounded (S₁ ; S₂)
--   1. finite S₁ , bounded S₂ : L$ S₁ η ⊃ ∅ , L$ S₂ η ⊆ { □ }
--      conc≤1 (L$ S₁ η) (L$ S₂ η) ⊆ { □ }
--   2. loops S₁ : L$ S₁ η = ∅ implies conc≤1 (L$ S₁ η) (L$ S₂ η) = ∅ ⊆ { □ }
-- rb (S₁ & S₂) = OK: by rb S₁ and rb S₂
-- rb (μX.S) = fixed point induction
--   base case: rb S η[ X ↦ ∅ ]
--         * dom-η′ is ok
--         * ass-X′ is ok by ass-X and η X ⊆ { □ }
--         * bs′ by inversion of bs
--   inductive case: if A ⊆ { □ } then rb S η[ X ↦ A ] ⊆ { □ }
