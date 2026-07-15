module bounded where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _⊔_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside; Side; _∈_; _∉_; _∪_; _─_; _-_; ⊥; _⊆_; ⁅_⁆; Nonempty)
open import Data.Fin.Subset.Properties using (nonempty?; _∈?_; ∪-idem; x∈⁅x⁆; x∈p∪q⁺; x∈p∪q⁻; ∉⊥; ⊥⊆; x∈p∧x≢y⇒x∈p-y; ∪-identityʳ; p─q⊆p; drop-∷-⊆)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Product using (∃; ∄; _×_; _,_; proj₁)
open import Data.Vec using (Vec; []; _∷_; _[_]=_; here; there; replicate)
open import Relation.Nullary using (¬_; contradiction; contraposition)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; subst; _≢_; sym)

--------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------
-- aux (Data.Subset.Properties)

∪-sup : ∀ {n} → (X Y Z : Subset n) → X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z
∪-sup X Y Z X⊆Z Y⊆Z x∈
  with x∈p∪q⁻ X Y x∈
... | inj₁ x∈X = X⊆Z x∈X
... | inj₂ x∈Y = Y⊆Z x∈Y

X-X : ∀ {n} (X : Subset n) → X ─ X ≡ ⊥
X-X [] = refl
X-X (outside ∷ X) = cong (outside ∷_) (X-X X)
X-X (inside ∷ X) = cong (outside ∷_) (X-X X)

⁅x⁆-x : ∀ {n : ℕ} {x : Fin n} → ⁅ x ⁆ - x ≡ ⊥
⁅x⁆-x {x = x} = X-X ⁅ x ⁆

∪-⊆ : ∀ {n} → (X Y : Subset n) → Y ⊆ X → X ∪ Y ≡ X
∪-⊆ [] [] Y⊆X = refl
∪-⊆ (outside ∷ X) (outside ∷ Y) Y⊆X = cong (outside ∷_) (∪-⊆ X Y (drop-∷-⊆ Y⊆X))
∪-⊆ (outside ∷ X) (inside ∷ Y) Y⊆X with Y⊆X here
... | ()
∪-⊆ (inside ∷ X) (outside ∷ Y) Y⊆X = cong (inside ∷_) (∪-⊆ X Y (drop-∷-⊆ Y⊆X))
∪-⊆ (inside ∷ X) (inside ∷ Y) Y⊆X = cong (inside ∷_) (∪-⊆ X Y (drop-∷-⊆ Y⊆X))

--------------------------------------------------------------------------------

variable
  n k : ℕ

-- k - variables
-- n - size of alphabet

data Session (n : ℕ) : (k : ℕ) → Set where
  `_      : Fin k → Session n k
  Skip    : Session n k
  Atom    : Fin n → Session n k
  Seq     : Session n k → Session n k → Session n k
  Choice  : Session n k → Session n k → Session n k
  Mu      : Session n (suc k) → Session n k


  
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

weps≢ : ∀ {y : Fin n} → suc y ≢ zero
weps≢ ()

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
... | yes zero∈ = X ∪ (Y - weps)

concSW : Sym n → WSet n → WSet n
concSW zero Y = Y
concSW (suc x) Y
  with weps ∈? Y
... | no weps∉ = Y
... | yes weps∈ = ⁅ suc x ⁆ ∪ Y

-- properties of conc and friends

concW↓₁' : {X Y : WSet n} → X ≡ ⊥ → concW X Y ≡ ⊥
concW↓₁' {n = n}{X = X}{Y = Y} X≡⊥
  with nonempty? X
... | no ¬a = refl
... | yes (x , x∈) rewrite X≡⊥ = contradiction x∈ ∉⊥

concW↓₁ : {Y : WSet n} → concW ⊥ Y ≡ ⊥
concW↓₁ {n = n}{Y = Y} = concW↓₁' {Y = Y} refl

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
concW↑ {x = zero} {y} x∈ y∈ | yes a | no weps∉ = y∈
concW↑ {x = suc x} {zero} x∈ y∈ | yes a | no weps∉ = contradiction y∈ weps∉
concW↑ {x = suc x} {suc y} x∈ y∈ | yes a | no weps∉ = y∈
concW↑ {x = zero} {zero} x∈ y∈ | yes a | yes weps∈ = x∈p∪q⁺ (inj₁ x∈)
concW↑ {x = zero} {suc y} x∈ y∈ | yes a | yes weps∈ = x∈p∪q⁺ (inj₂ (x∈p∧x≢y⇒x∈p-y y∈ weps≢))
concW↑ {x = suc x} {zero} x∈ y∈ | yes a | yes weps∈ = x∈p∪q⁺ (inj₁ x∈)
concW↑ {x = suc x} {suc y} x∈ y∈ | yes a | yes weps∈ = x∈p∪q⁺ (inj₂ (x∈p∧x≢y⇒x∈p-y {y = weps} y∈ weps≢))


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

concW⊆ : ∀ {s} {X Y : WSet n} → Y ⊆ ⁅ suc s ⁆ → concW X Y ⊆ ⁅ suc s ⁆
concW⊆ {n} {s} {X} {Y} Y⊆
  with nonempty? X
... | no ¬a = λ x∈⊥ → contradiction x∈⊥ ∉⊥
... | yes a
  with weps ∈? Y
... | no weps∉ = Y⊆
... | yes weps∈ = contradiction weps∈ (lemma0 Y⊆)

lemma3 : ∀ {n}{X : Subset n} → (∄ λ x → x ∈ X) → ⊥ ≡ X
lemma3 {X = []} x = refl
lemma3 {X = outside ∷ X} x = cong (outside ∷_) (lemma3 (λ{ (fst , snd) → x ((suc fst) , (there snd))}))
lemma3 {X = inside ∷ X} x = ⊥-elim (x (zero , here))

concWε : ∀ {X Y : WSet n} → Y ≡ ⁅ weps ⁆ → concW X Y ≡ X
concWε {n}{X}{Y} Y≡ε
  with nonempty? X
... | no ¬a = lemma3 ¬a
... | yes a
  with weps ∈? Y
... | no weps∉ rewrite Y≡ε = ⊥-elim (weps∉ here)
... | yes weps∈ rewrite Y≡ε | ⁅x⁆-x {x = weps{n}} = ∪-identityʳ X


--------------------------------------------------------------------------------
-- WSet is a pointed CPO (actually a complete lattice)
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
  L$ (` x) η          = η x
  L$ Skip η           = ⁅ weps ⁆
  L$ (Atom x) η       = ⁅ suc (suc x) ⁆
  L$ (Seq S S₁) η     = concW (L$ S η) (L$ S₁ η)
  L$ (Choice S S₁) η  = concSW inlr (L$ S η) ∪ concSW inlr (L$ S₁ η)
  L$ (Mu S) η         = fix (λ A → L$ S (ext η A))

-- version with step count

fixᵢ : (WSet n → ℕ → WSet n) → ℕ → WSet n
fixᵢ f zero     = f ⊥ zero          -- standard: ⊥, but this is also correct
fixᵢ f (suc i)  = f (fixᵢ f i) i


L$ : Session n k → (Fin k → WSet n) → ℕ → WSet n
L$ (` x) η i          = η x
L$ Skip η i           = ⁅ weps ⁆
L$ (Atom x) η i       = ⁅ suc (suc x) ⁆
L$ (Seq S S₁) η i     = concW (L$ S η i) (L$ S₁ η i)
L$ (Choice S S₁) η i  = concSW inlr (L$ S η i) ∪ concSW inlr (L$ S₁ η i)
L$ (Mu S) η i         = fixᵢ (λ A → L$ S (ext η A)) i

variable
  S S₁ S₂ : Session n k

--------------------------------------------------------------------------------
-- several inductively defined properties with soundness proofs wrt the trace semantics

-- session types generating the empty trace

data skips : Session n k → Set where

  skips-Skip  : skips {n} {k} Skip

  skips-Seq   : skips S₁ → skips S₂ → skips (Seq S₁ S₂)

  skips-Mu    : skips S → skips (Mu S)

sound-skips : (S : Session n k) (η : Fin k → WSet n) → skips S
  → ∀ i → L$ S η i ≡ ⁅ weps ⁆

sound-skips-fix : (S : Session n (suc k)) (η : Fin k → WSet n) → skips S
  → ∀ i → fixᵢ (λ A → L$ S (ext η A)) i ≡ ⁅ weps ⁆

sound-skips (` x) η () i
sound-skips Skip η skips-Skip i = refl
sound-skips (Atom x) η () i
sound-skips (Seq S S₁) η (skips-Seq sk sk₁) i
  rewrite sound-skips S η sk i | sound-skips S₁ η sk₁ i
  = ∪-⊆ ⁅ weps ⁆ (⁅ weps ⁆ - weps) (p─q⊆p ⁅ weps ⁆ ⁅ weps ⁆)
sound-skips (Choice S S₁) η () i
sound-skips (Mu S) η (skips-Mu sk) i = sound-skips-fix S η sk i

sound-skips-fix S η sk zero = sound-skips S (ext η ⊥) sk zero
sound-skips-fix S η sk (suc i) = sound-skips S (ext η (fixᵢ (λ A → L$ S (ext η A)) i)) sk i

-- session types generating at least one finite trace

data finite : Session n k → Set where

  finite-Skip   : finite{n}{k} Skip

  finite-Atom   : ∀ {a : Fin n} → finite{n}{k} (Atom a)

  finite-Seq    : finite S₁ → finite S₂ → finite (Seq S₁ S₂)

  finite-Left   : finite S₁ → finite (Choice S₁ S₂)

  finite-Right  : finite S₂ → finite (Choice S₁ S₂)

  finite-Mu     : finite S → finite (Mu S)

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

  loops-var        : ∀ {x} → loops{n}{k} (` x)

  loops-seq-left   : loops S₁ → loops (Seq S₁ S₂)

  loops-seq-right  : loops S₂ → loops (Seq S₁ S₂)

  loops-choice     : loops S₁ → loops S₂ → loops (Choice S₁ S₂)

  loops-Mu         : loops S → loops (Mu S)

sound-loops : {S : Session n k} (η : Fin k → WSet n) (ass-η : ∀ x → η x ≡ ⊥) (lps : loops S)
  → ∀ i → L$ S η i ≡ ⊥

sound-loops-fix : {S : Session n (suc k)} (η : Fin k → WSet n) (ass-η : ∀ x → η x ≡ ⊥) (lps : loops S)
  → ∀ i → fixᵢ (λ A → L$ S (ext η A)) i ≡ ⊥

sound-loops η ass-η loops-var i = ass-η _
sound-loops η ass-η (loops-seq-left lps) i
  rewrite sound-loops η ass-η lps i
  = concW↓₁
sound-loops {S = Seq S₁ S₂} η ass-η (loops-seq-right lps) i
  rewrite sound-loops η ass-η lps i = concW↓₂ {X = L$ S₁ η i}
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

  bounded-var     : ∀ {x} → bounded{n}{k} (` x)

  bounded-close   : bounded{n}{k} (Atom zero) -- clos

  bounded-seq-2   : bounded S₂ → bounded (Seq S₁ S₂)

  --  I believe this is fine, but can't prove it
  --  bounded-loop-seq : loops S₁ → bounded (Seq S₁ S₂)

  bounded-seq-1   : bounded S₁ → skips S₂ → bounded (Seq S₁ S₂)

  bounded-choice  : bounded S₁ → bounded S₂ → bounded (Choice S₁ S₂)

  bounded-mu      : bounded S → bounded (Mu S)


sound-bounded : {S : Session (suc n) k}
  → (η : Fin k → WSet (suc n))
  → (ass-η : ∀ x → η x ⊆ ⁅ clos ⁆)
  → (bs : bounded S)
  → ∀ i → L$ S η i ⊆ ⁅ clos ⁆

sound-bounded-fix : {S : Session (suc n) (suc k)}
  → (η : Fin k → WSet (suc n))
  → (ass-η : ∀ x → η x ⊆ ⁅ clos ⁆)
  → (bs : bounded S)
  → ∀ i → fixᵢ (λ A → L$ S (ext η A)) i ⊆ ⁅ clos ⁆

sound-bounded η ass-η bounded-var i = ass-η _
sound-bounded η ass-η bounded-close i x = x
sound-bounded {S = Seq S₁ S₂} η ass-η (bounded-seq-2 bs) i
  with sound-bounded η ass-η bs i
... | iv = concW⊆{s = suc zero}{X = L$ S₁ η i} iv
-- sound-bounded {S = Seq S₁ S₂} η ass-η (bounded-loop-seq lps) i
--   rewrite sound-loops η {!!} lps i
--   rewrite concW↓₁ {Y = L$ S₂ η i} = ⊥⊆
sound-bounded {S = Seq S₁ S₂} η ass-η (bounded-seq-1 bs sks) i
  rewrite sound-skips S₂ η sks i | concWε {X = L$ S₁ η i} refl = sound-bounded η ass-η bs i

sound-bounded η ass-η (bounded-choice bs bs₁) i
  with sound-bounded η ass-η bs i | sound-bounded η ass-η bs₁ i
... | iv | iv₁
  = ∪-sup _ _ _ (concSW⊆{s = suc zero} iv) (concSW⊆{s = suc zero} iv₁)
sound-bounded η ass-η (bounded-mu bs) i = sound-bounded-fix η ass-η bs i

sound-bounded-fix η ass-η bs zero = sound-bounded (ext η ⊥) (λ{ zero → ⊥⊆ ; (suc x) → ass-η x}) bs zero
sound-bounded-fix {S = S} η ass-η bs (suc i) = sound-bounded (ext η (fixᵢ (λ A → L$ S (ext η A)) i)) (λ{ zero → sound-bounded-fix η ass-η bs i ; (suc x) → ass-η x}) bs i
