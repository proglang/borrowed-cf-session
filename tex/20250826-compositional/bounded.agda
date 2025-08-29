module bounded where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _⊔_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside; _∈_; _∉_; _∪_; ⊥; _⊆_; ⁅_⁆; Nonempty)
open import Data.Fin.Subset.Properties using (nonempty?; _∈?_; ∪-idem; x∈⁅x⁆; x∈p∪q⁺; x∈p∪q⁻; ∉⊥; ⊥⊆)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Product using (∃; ∄; _×_; _,_; proj₁)
open import Data.Vec using (_∷_; _[_]=_; here; there)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; subst; _≢_; sym)

-- aux (overlap Data.Nat.Properties)
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

-- aux (Data.Subset.Properties)

∪-sup : ∀ {n} → (X Y Z : Subset n) → X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z
∪-sup X Y Z X⊆Z Y⊆Z x∈
  with x∈p∪q⁻ X Y x∈
... | inj₁ x∈X = X⊆Z x∈X
... | inj₂ x∈Y = Y⊆Z x∈Y

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

inlr : Sym n
inlr = suc zero

-- concatenation of last symbols
conc : Sym n → Sym n → Sym n
conc zero y = y
conc (suc x) zero = suc x
conc (suc x) (suc y) = suc y

conc-≡ : (x : Sym n) → conc x zero ≡ x
conc-≡ zero = refl
conc-≡ (suc x) = refl

-- can add conc-≡ as a rewrite

-- concW : WSet n → WSet n → WSet n
-- concW x y = { conc a? b? ∣ a? ∈ x, b? ∈ y }

concW : WSet n → WSet n → WSet n
concW X Y
  with nonempty? X
... | no ¬a = ⊥
... | yes a
  with weps ∈? Y
... | no zero∉ = Y
... | yes zero∈ = X ∪ Y

concSW : Sym n → WSet n → WSet n
concSW zero Y = Y
concSW (suc x) Y
  with weps ∈? Y
... | no weps∉ = Y
... | yes weps∈ = ⁅ suc x ⁆ ∪ Y

-- properties

concW↓₁ : {Y : WSet n} → concW ⊥ Y ≡ ⊥
concW↓₁ {n = n}{Y = Y}
  with nonempty?{n} ⊥
... | yes (x , x∈⊥) = contradiction x∈⊥ ∉⊥
... | no ¬a = {!!}

concW↓₂ : {X : WSet n} → concW X ⊥ ≡ ⊥
concW↓₂ {n = n}{X = X}
  with nonempty? X
... | no ¬a = refl
... | yes a
  with weps{n} ∈? ⊥
... | no ¬b = refl
... | yes ε∈⊥ = contradiction ε∈⊥ ∉⊥

concSW↓ : (x : Sym n) → concSW x ⊥ ≡ ⊥
concSW↓ zero = refl
concSW↓ {n} (suc x)
  with weps{n} ∈? ⊥
... | no ¬a = refl
... | yes a = refl

concW↑ : {X Y : WSet n} → ∀ {x y} → x ∈ X → y ∈ Y → conc x y ∈ concW X Y
concW↑ {X = X}{Y = Y}{x}{y} x∈ y∈
  with nonempty? X
... | no ¬a = ⊥-elim (¬a (_ , x∈))
... | yes a
  with weps ∈? Y
concW↑ {X = X} {Y = Y} {zero} {y} x∈ y∈ | yes a | no weps∉ = y∈
concW↑ {X = X} {Y = Y} {suc x} {zero} x∈ y∈ | yes a | no weps∉ = contradiction y∈ weps∉
concW↑ {X = X} {Y = Y} {suc x} {suc y} x∈ y∈ | yes a | no weps∉ = y∈
concW↑ {X = X} {Y = Y} {zero} {y} x∈ y∈ | yes a | yes weps∈ = x∈p∪q⁺ (inj₂ y∈)
concW↑ {X = X} {Y = Y} {suc x} {zero} x∈ y∈ | yes a | yes weps∈ = x∈p∪q⁺ (inj₁ x∈)
concW↑ {X = X} {Y = Y} {suc x} {suc y} x∈ y∈ | yes a | yes weps∈ = x∈p∪q⁺ (inj₂ y∈)

concSW↑ : {Y : WSet n} → ∀ x {y} → y ∈ Y → conc x y ∈ concSW x Y
concSW↑ {Y = Y} zero {y} y∈ = y∈
concSW↑ {Y = Y} (suc x) {y} y∈
  with weps ∈? Y
concSW↑ {Y = Y} (suc x) {zero} y∈ | no weps∉ = contradiction y∈ weps∉
concSW↑ {Y = Y} (suc x) {suc y} y∈ | no weps∉ = y∈
concSW↑ {Y = Y} (suc x) {zero} y∈ | yes weps∈ = x∈p∪q⁺ (inj₁ (there (x∈⁅x⁆ x)))
concSW↑ {Y = Y} (suc x) {suc y} y∈ | yes weps∈ = x∈p∪q⁺ (inj₂ y∈)

lemma1 : ∀ {s : Fin (suc n)} → weps ∉ outside ∷ ⁅ s ⁆
lemma1 ()
lemma0 : ∀ {s} {Y : WSet n} → Y ⊆ ⁅ suc s ⁆ → weps ∉ Y
lemma0 Y⊆ ε∈ = contradiction (Y⊆ ε∈) lemma1


concSW⊆ : ∀ {s} {Y : WSet n} → Y ⊆ ⁅ suc s ⁆ → concSW inlr Y ⊆ ⁅ suc s ⁆
concSW⊆ {Y = Y} Y⊆ x∈
  with weps ∈? Y
... | no ¬a = Y⊆ x∈
... | yes a = contradiction a (lemma0 Y⊆)


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


ext : ∀ {A : Set} → (Fin k → A) → A → (Fin (suc k) → A)
ext η a zero = a
ext η a (suc i) = η i


module specification where
  postulate
    fix : ∀ {A : Set} → (A → A) → A

  L$ : Session n k → (Fin k → WSet n) → WSet n
  L$ (` x) η = η x
  L$ Skip η = ⁅ weps ⁆
  L$ (Atom x) η = ⁅ suc (suc x) ⁆
  L$ (Seq S S₁) η = concW (L$ S η) (L$ S₁ η)
  L$ (Choice S S₁) η = concSW inlr (L$ S η) ∪ concSW inlr (L$ S₁ η)
  L$ (Mu S) η = fix (λ A → L$ S (ext η A))

-- version with step count

fixᵢ : (WSet n → ℕ → WSet n) → ℕ → WSet n
fixᵢ f zero = f ⊥ zero          -- was ⊥
fixᵢ f (suc i) = f (fixᵢ f i) i


L$ : Session n k → (Fin k → WSet n) → ℕ → WSet n
L$ (` x) η i = η x
L$ Skip η i = ⁅ weps ⁆
L$ (Atom x) η i = ⁅ suc (suc x) ⁆
L$ (Seq S S₁) η i = concW (L$ S η i) (L$ S₁ η i)
L$ (Choice S S₁) η i = concSW inlr (L$ S η i) ∪ concSW inlr (L$ S₁ η i)
L$ (Mu S) η i = fixᵢ (λ A → L$ S (ext η A)) i

variable
  S S₁ S₂ : Session n k

-- session types generating the empty trace

data skips : Session n k → Set where

  skips-Skip : skips {n} {k} Skip

  skips-Seq  : skips S₁ → skips S₂ → skips (Seq S₁ S₂)

  skips-Mu   : skips S → skips (Mu S)

sound-skips-fix : (S : Session n (suc k)) (η : Fin k → WSet n) → skips S
  → ∀ i → fixᵢ (λ A → L$ S (ext η A)) i ≡ ⁅ weps ⁆
sound-skips : (S : Session n k) (η : Fin k → WSet n) → skips S
  → ∀ i → L$ S η i ≡ ⁅ weps ⁆

sound-skips (` x) η () i
sound-skips Skip η skips-Skip i = refl
sound-skips (Atom x) η () i
sound-skips (Seq S S₁) η (skips-Seq sk sk₁) i
  rewrite sound-skips S η sk i | sound-skips S₁ η sk₁ i
  = ∪-idem ⁅ weps ⁆
sound-skips (Choice S S₁) η () i
sound-skips (Mu S) η (skips-Mu sk) i = sound-skips-fix S η sk i

sound-skips-fix S η sk zero = sound-skips S (ext η ⊥) sk zero
sound-skips-fix S η sk (suc i) = sound-skips S (ext η (fixᵢ (λ A → L$ S (ext η A)) i)) sk i

-- session types generating at least one finite trace

data finite : Session n k → Set where

  finite-Skip : finite{n}{k} Skip

  finite-Atom : ∀ {a : Fin n} → finite{n}{k} (Atom a)

  finite-Seq : finite S₁ → finite S₂ → finite (Seq S₁ S₂)

  finite-Left : finite S₁ → finite (Choice S₁ S₂)

  finite-Right : finite S₂ → finite (Choice S₁ S₂)

  finite-Mu : finite S → finite (Mu S)

sound-finite : {S : Session n k} → (η : Fin k → WSet n) → (fn : finite S)
  → ∀ i → Nonempty (L$ S η i)
sound-finite-fix : {S : Session n (suc k)} → (η : Fin k → WSet n) → (fn : finite S)
  → ∀ i → Nonempty (fixᵢ (λ A → L$ S (ext η A)) i)

sound-finite η finite-Skip i = weps , here
sound-finite {S = Atom a} η finite-Atom i = suc (suc a) , x∈⁅x⁆ (suc (suc a))
sound-finite η (finite-Seq fn fn₁) i
  with sound-finite η fn i | sound-finite η fn₁ i
... | x , x∈ | y , y∈
  = conc x y , concW↑ x∈ y∈
sound-finite η (finite-Left fn) i
  with sound-finite η fn i
... | zero , x∈ = inlr , x∈p∪q⁺ (inj₁ (concSW↑ inlr x∈))
... | suc x , x∈ = suc x , x∈p∪q⁺ (inj₁ (concSW↑ inlr x∈))
sound-finite η (finite-Right fn) i
  with sound-finite η fn i
... | zero , x∈ = inlr , x∈p∪q⁺ (inj₂ (concSW↑ inlr x∈))
... | suc x , x∈ = suc x , x∈p∪q⁺ (inj₂ (concSW↑ inlr x∈))
sound-finite η (finite-Mu fn) i = sound-finite-fix η fn i

sound-finite-fix η fn zero = sound-finite (ext η ⊥) fn zero
sound-finite-fix {S = S} η fn (suc i) = sound-finite (ext η (fixᵢ (λ A → L$ S (ext η A)) i)) fn i

-- session types generating only infinite traces

data loops : Session n k → Set where

  loops-var : ∀ {x} → loops{n}{k} (` x)

  loops-seq-left : loops S₁ → loops (Seq S₁ S₂)

  loops-seq-right : finite S₁ → loops S₂ → loops (Seq S₁ S₂)

  loops-choice : loops S₁ → loops S₂ → loops (Choice S₁ S₂)

  loops-Mu : loops S → loops (Mu S)

sound-loops : {S : Session n k} (η : Fin k → WSet n) (ass-η : ∀ x → η x ≡ ⊥) (lps : loops S)
  → ∀ i → L$ S η i ≡ ⊥

sound-loops-fix : {S : Session n (suc k)} (η : Fin k → WSet n) (ass-η : ∀ x → η x ≡ ⊥) (lps : loops S)
  → ∀ i → fixᵢ (λ A → L$ S (ext η A)) i ≡ ⊥

sound-loops η ass-η loops-var i = ass-η _
sound-loops η ass-η (loops-seq-left lps) i
  rewrite sound-loops η ass-η lps i
  = concW↓₁
sound-loops η ass-η (loops-seq-right fn lps) i = {!!}
sound-loops η ass-η (loops-choice lps lps₁) i
  rewrite sound-loops η ass-η lps i | sound-loops η ass-η lps₁ i
  = ∪-idem ⊥
sound-loops η ass-η (loops-Mu lps) i = sound-loops-fix η ass-η lps i

sound-loops-fix η ass-η lps zero = sound-loops (ext η ⊥) (λ{ zero → refl ; (suc x) → ass-η x}) lps zero
sound-loops-fix {S = S} η ass-η lps (suc i)
  rewrite sound-loops-fix η ass-η lps i
  = sound-loops (ext η ⊥) (λ{ zero → refl ; (suc x) → ass-η x}) lps i

-- bounded session types

clos : Sym (suc n)
clos = suc (suc zero)

data bounded : Session (suc n) k → Set where

  bounded-var : ∀ {x} → bounded{n}{k} (` x)

  bounded-close : bounded{n}{k} (Atom zero) -- clos

  bounded-finite-seq : finite S₁ → bounded S₂ → bounded (Seq S₁ S₂)

  bounded-loop-seq : loops S₁ → bounded (Seq S₁ S₂)

  bounded-choice : bounded S₁ → bounded S₂ → bounded (Choice S₁ S₂)

  bounded-mu : bounded S → bounded (Mu S)

sound-bounded : {S : Session (suc n) k}
  → (η : Fin k → WSet (suc n))
  → (ass-η : ∀ x → η x ⊆ ⁅ clos ⁆)
  → (bs : bounded S)
  → ∀ i → L$ S η i ⊆ ⁅ clos ⁆
sound-bounded η ass-η bounded-var i = ass-η _
sound-bounded η ass-η bounded-close i x = x
sound-bounded η ass-η (bounded-finite-seq fn bs) i x = {!!}
sound-bounded {S = Seq S₁ S₂} η ass-η (bounded-loop-seq lps) i
  rewrite sound-loops η {!!} lps i
  rewrite concW↓₁ {Y = L$ S₂ η i} = ⊥⊆
sound-bounded η ass-η (bounded-choice bs bs₁) i
  with sound-bounded η ass-η bs i | sound-bounded η ass-η bs₁ i
... | iv | iv₁
  = ∪-sup _ _ _ (concSW⊆{s = suc zero} iv) (concSW⊆{s = suc zero} iv₁)
sound-bounded η ass-η (bounded-mu bs) i x = {!!}

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
