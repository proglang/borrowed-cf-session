open import BorrowedCF.Prelude

module BorrowedCF.Types.Atoms (front : Bool) where

open import Data.Bool using () renaming (T to 𝔗)
open import Data.Bool.Properties


open import BorrowedCF.Types.Syntax hiding (a)
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomSnoc using (ClosedAtom)
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc; closedatom-atom)
open import BorrowedCF.Types.AtomCons using (atom-;-cons)

open Nat.Variables
open ≃-Reasoning

infixl 17 _⨟_

if-true : ∀ {a} {A : Set a} {b} → b ≡ true → {x : A} (y : A) → (if b then x else y) ≡ x
if-true refl y = refl

if-false : ∀ {a} {A : Set a} {b} → b ≡ false → (x : A) {y : A} → (if b then x else y) ≡ y
if-false refl x = refl

if-simp : ∀ {a} {A : Set a} b {x x′ y y′ : A} → (b ≡ true → x ≡ x′) → (b ≡ false → y ≡ y′) →
  (if b then x else y) ≡ (if b then x′ else y′)
if-simp true  eqˣ eqʸ = eqˣ refl
if-simp false eqˣ eqʸ = eqʸ refl

if-cong-≃ : ∀ b →
  s₁ ≃ s₁′ →
  s₂ ≃ s₂′ →
  (if b then s₁ else s₂) ≃ (if b then s₁′ else s₂′)
if-cong-≃ true  eq₁ eq₂ = eq₁
if-cong-≃ false eq₁ eq₂ = eq₂

if-select : ∀ {ℓ} {A B : Set ℓ} b → A → B → if b then A else B
if-select true  x y = x
if-select false x y = y

_⨟_ : 𝕊 n → 𝕊 n → 𝕊 n
x ⨟ y = if front then x ; y else y ; x

⨟-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → (s₁ ⨟ s₂) ⋯ ϕ ≡ (s₁ ⋯ ϕ) ⨟ (s₂ ⋯ ϕ)
⨟-⋯ {ϕ = ϕ} = if-float (_⋯ ϕ) front

⨟-assoc : (s₁ ⨟ s₂) ⨟ s₃ ≃ s₁ ⨟ (s₂ ⨟ s₃)
⨟-assoc {s₁ = s₁}{s₂}{s₃} = begin
  (s₁ ⨟ s₂) ⨟ s₃
    ≡⟨ if-simp front (λ eq → cong (_; s₃) (if-true eq _)) (λ eq → cong (s₃ ;_) (if-false eq _)) ⟩
  (if front then (s₁ ; s₂) ; s₃ else s₃ ; (s₂ ; s₁))
    ≈⟨ if-cong-≃ front ≃-assoc-; (≃-sym ≃-assoc-;) ⟩
  (if front then s₁ ; (s₂ ; s₃) else (s₃ ; s₂) ; s₁)
    ≡⟨ if-simp front (λ eq → cong (s₁ ;_) (if-true eq _)) (λ eq → cong (_; s₁) (if-false eq _)) ⟨
  s₁ ⨟ (s₂ ⨟ s₃) ∎

⨟-skipˡ : skip ⨟ s ≃ s
⨟-skipˡ {s = s} rewrite if-float (_≃ s) front {skip ; s} {s ; skip} =
  if-select front ≃-skipˡ ≃-skipʳ

⨟-skipʳ : s ⨟ skip ≃ s
⨟-skipʳ {s = s} rewrite if-float (_≃ s) front {s ; skip} {skip ; s} =
  if-select front ≃-skipʳ ≃-skipˡ

⨟-cong : s₁ ≃ s₁′ → s₂ ≃ s₂′ → s₁ ⨟ s₂ ≃ s₁′ ⨟ s₂′
⨟-cong {s₁ = s₁} {s₁′} {s₂} {s₂′} eq₁ eq₂
  rewrite if-float (s₁ ⨟ s₂ ≃_) front {s₁′ ; s₂′} {s₂′ ; s₁′}
  = subst id (sym (if-simp front (λ eq → cong (_≃ s₁′ ; s₂′) (if-true eq _))
                                 λ eq → cong (_≃ s₂′ ; s₁′) (if-false eq _)))
             (if-select front (≃-; eq₁ eq₂) (≃-; eq₂ eq₁))

⨟-cong₁ : s₁ ≃ s₂ → s₁ ⨟ s ≃ s₂ ⨟ s
⨟-cong₁ eq = ⨟-cong eq ≃-refl

⨟-cong₂ : s₁ ≃ s₂ → s ⨟ s₁ ≃ s ⨟ s₂
⨟-cong₂ eq = ⨟-cong ≃-refl eq

Front = 𝔗 front
Back  = ¬ Front  -- or: 𝔗 (not front)

Front-≡ : Front → front ≡ true
Front-≡ = Equivalence.to T-≡

Back-≡ : Back → front ≡ false
Back-≡ = go front where
  go : ∀ b → ¬ 𝔗 b → b ≡ false
  go true  ¬T = contradiction _ ¬T
  go false ¬T = refl

⨟-distr : Back → s ⨟ brn p s₁ s₂ ≃ brn p (s ⨟ s₁) (s ⨟ s₂)
⨟-distr b rewrite Back-≡ b = ≃-distr

⨟-back : Back → s₁ ⨟ s₂ ≡ s₂ ; s₁
⨟-back x rewrite Back-≡ x = refl

⨟-front : Front → s₁ ⨟ s₂ ≡ s₁ ; s₂
⨟-front x rewrite Front-≡ x = refl

private variable a : 𝕊 n

-- Cat a x y witnesses the equivalence a ⨟ x ≃ y.

data Cat (a : 𝕊 n) : 𝕊 n → 𝕊 n → Set where
  here : a ≃ s → Cat a skip s

  mu  : Cat (a ⋯ weakenᵣ) s s′ → Cat a (s ⋯ ⦅ mu s′ ⦆) (mu s′)
  brn : (B : Back) → Cat a s₁ s₁′ → Cat a s₂ s₂′ → Cat a (brn p s₁ s₂) (brn p s₁′ s₂′)

  back_∶_;₁_ : (B : Back) → Cat a s s₁ → Skips s₂ → Cat a s (s₁ ; s₂)
  back_∶-;₂_ : (B : Back) → Cat a s s₂ → Cat a (s₁ ; s) (s₁ ; s₂)

  front_∶_;₁- : (F : Front) → Cat a s s₁ → Cat a (s ; s₂) (s₁ ; s₂)
  front_∶_;₂_ : (F : Front) → Skips s₁ → Cat a s s₂ → Cat a s (s₁ ; s₂)

cat-sound : Cat a s′ s → a ⨟ s′ ≃ s
cat-sound (here eq) = ≃-trans ⨟-skipʳ eq
cat-sound (brn bk x₁ x₂) = ≃-trans (⨟-distr bk) (≃-brn (cat-sound x₁) (cat-sound x₂))
cat-sound (mu {s′} {s} x) = ≃-sym $ ≃-trans ≃-μ $
  subst (unfold s ≃_)
        (⨟-⋯ ■ cong (_⨟ (s′ ⋯ ⦅ mu s ⦆)) (wk-cancels-⦅⦆-⋯ _ _))
        (≃-sym (≃-⋯ (cat-sound x)))
cat-sound (back B ∶ x ;₁ y) = ≃-trans (cat-sound x) (≃-sym (≃-skipsʳ y))
cat-sound (back B ∶-;₂ y) =
  ≃-trans (≃-trans (≃-reflexive (⨟-back B)) (≃-trans ≃-assoc-; (≃-; ≃-refl (≃-reflexive (sym (⨟-back B))))))
          (≃-; ≃-refl (cat-sound y))
cat-sound (front F ∶ x ;₁-) =
  ≃-trans (≃-trans (≃-reflexive (⨟-front F)) (≃-trans (≃-sym ≃-assoc-;) (≃-; (≃-reflexive (sym (⨟-front F))) ≃-refl)))
          (≃-; (cat-sound x) ≃-refl)
cat-sound (front F ∶ x ;₂ y) = ≃-trans (cat-sound y) (≃-sym (≃-skipsˡ x))

cat-⋯ : {ϕ : m →ₛ n} → Cat a s s′ → Cat (a ⋯ ϕ) (s ⋯ ϕ) (s′ ⋯ ϕ)
cat-⋯ (here eq) = here (≃-⋯ eq)
cat-⋯ (brn x c₁ c₂) = brn x (cat-⋯ c₁) (cat-⋯ c₂)
cat-⋯ (back B ∶ c ;₁ z) = back B ∶ cat-⋯ c ;₁ skips-⋯ z
cat-⋯ (back B ∶-;₂ c) = back B ∶-;₂ cat-⋯ c
cat-⋯ (front F ∶ c ;₁-) = front F ∶ cat-⋯ c ;₁-
cat-⋯ (front F ∶ z ;₂ c) = front F ∶ skips-⋯ z ;₂ cat-⋯ c
cat-⋯ {a = a} {ϕ = ϕ} (mu {s} {s′} c) =
  subst (λ s₀ → Cat _ s₀ _)
    (sym (dist-↑-⦅⦆-⋯ s (mu s′) ϕ))
    (mu (subst (λ a₀ → Cat a₀ _ _) (sym (⋯-↑-wk a ϕ)) (cat-⋯ c)))

cat-unfold : Atom a → Cat a s (mu s′) → Cat a s (unfold s′)
cat-unfold A (mu c) = subst (λ a → Cat a _ _) (wk-cancels-⦅⦆-⋯ _ _) (cat-⋯ c)
cat-unfold A (here eq) = here (≃-trans eq ≃-μ)

cat-¬skips : Atom a → Cat a s s′ → ¬ Skips s′
cat-¬skips A (here eq)          z         = ¬skips-atom A (≃-skips (≃-sym eq) z)
cat-¬skips A (mu c)             (mu z)    = cat-¬skips (atom-⋯ᵣ A) c z
cat-¬skips A (back B ∶ c ;₁ x)  (z₁ ; z₂) = cat-¬skips A c z₁
cat-¬skips A (back B ∶-;₂ c)    (z₁ ; z₂) = cat-¬skips A c z₂
cat-¬skips A front F ∶ c ;₁-    (z₁ ; z₂) = cat-¬skips A c z₁
cat-¬skips A (front F ∶ x ;₂ c) (z₁ ; z₂) = cat-¬skips A c z₂

-- The unfinished cat-≃ transport formerly in this module tried to combine the
-- front and back atom-peeling arguments under one generic relation.  The two
-- orientations need different invariants: the front split is only available
-- for closed non-msg atoms, while the back split works for any atom.  The
-- public split below therefore delegates to those completed developments and
-- exposes the strongest common sound interface.

atom-drop-front : ClosedAtom a → (∀ {p T} → a ≢ msg p T) →
  a ; s ≃ s₁ ; s₂ →
  Skips s₁ ⊎ ∃[ s′ ] a ; s′ ≃ s₁ × s ≃ s′ ; s₂
atom-drop-front ca nm eq with atom-;-cons ca nm (≃-sym eq)
... | inj₁ (z₁ , _) = inj₁ z₁
... | inj₂ (s′ , eq₁ , eq₂) = inj₂ (s′ , ≃-sym eq₁ , ≃-sym eq₂)

atom-drop-back : Atom a →
  s ; a ≃ s₂ ; s₁ →
  Skips s₁ ⊎ ∃[ s′ ] s′ ; a ≃ s₁ × s ≃ s₂ ; s′
atom-drop-back A eq with atom-;-unsnoc A (≃-sym eq)
... | inj₁ z₁ = inj₁ z₁
... | inj₂ (s′ , eq₁ , eq₂) = inj₂ (s′ , eq₂ , ≃-sym eq₁)

atom-drop′ : ∀ b → ClosedAtom a → (∀ {p T} → a ≢ msg p T) →
  (if b then a ; s else s ; a) ≃ (if b then s₁ ; s₂ else s₂ ; s₁) →
  Skips s₁ ⊎
  ∃[ s′ ] (if b then a ; s′ else s′ ; a) ≃ s₁ ×
           s ≃ (if b then s′ ; s₂ else s₂ ; s′)
atom-drop′ true  ca nm eq = atom-drop-front ca nm eq
atom-drop′ false ca nm eq = atom-drop-back (closedatom-atom ca) eq

atom-drop : ClosedAtom a → (∀ {p T} → a ≢ msg p T) →
  a ⨟ s ≃ s₁ ⨟ s₂ →
  Skips s₁ ⊎ ∃[ s′ ] a ⨟ s′ ≃ s₁ × s ≃ s′ ⨟ s₂
atom-drop = atom-drop′ front
