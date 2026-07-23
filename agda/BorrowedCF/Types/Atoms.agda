open import BorrowedCF.Prelude

module BorrowedCF.Types.Atoms (front : Bool) where

open import Data.Bool using () renaming (T to 𝔗)
open import Data.Bool.Properties
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)


open import BorrowedCF.Types.Syntax hiding (a)
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence

open Bin
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

-- Cat a x y witnesses the equivalence a ⨟ x ≃ y

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
cat-⋯ (here eq) = (here (≃-⋯ eq))
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

cat-≃ : Atom a → s₁ ≃ s₂ → Cat a s s₁ → ∃[ s′ ] s ≃ s′ × Cat a s′ s₂
cat-≃ A refl c = _ , refl , c
cat-≃ {a = a} A (x ◅ xs) c =
  let _ , eq₁ , c′ = go x c in
  let _ , eq₂ , c″ = cat-≃ A xs c′ in
  _ , ≃-trans eq₁ eq₂ , c″
  where
  go : SymClosure _≃𝕊_ s₁ s₂ → Cat a s s₁ → ∃[ s′ ] s ≃ s′ × Cat a s′ s₂
  go x (here eq) = skip , refl , here (≃-trans eq (Star.return x))
  go (fwd ≃𝕊-μ) c = _ , ≃-refl , cat-unfold A c

  go (fwd (≃𝕊-brn₁ x)) (brn B c₁ c₂) = Π.map _ (Π.map ≃-brn₁ λ c → brn B c c₂) (go (fwd x) c₁)
  go (fwd (≃𝕊-brn₂ x)) (brn B c₁ c₂) = Π.map _ (Π.map ≃-brn₂ λ c → brn B c₁ c) (go (fwd x) c₂)
  go (bwd (≃𝕊-brn₁ x)) (brn B c₁ c₂) = Π.map _ (Π.map ≃-brn₁ λ c → brn B c c₂) (go (bwd x) c₁)
  go (bwd (≃𝕊-brn₂ x)) (brn B c₁ c₂) = Π.map _ (Π.map ≃-brn₂ λ c → brn B c₁ c) (go (bwd x) c₂)

  go (fwd (≃𝕊-;₁ x)) (back B ∶ c ;₁ z)  = Π.map _ (Π.map₂ (back B ∶_;₁ z)) (go (fwd x) c)
  go (fwd (≃𝕊-;₂ x)) (back B ∶ c ;₁ z)  = _ , refl , back B ∶ c ;₁ ≃-skips (Eq*.return x) z
  go (fwd (≃𝕊-;₁ x)) (back B ∶-;₂ c)    = _ , ≃-; (Eq*.return x) refl , (back B ∶-;₂ c)
  go (fwd (≃𝕊-;₂ x)) (back B ∶-;₂ c)    = Π.map _ (Π.map (≃-; refl) (back B ∶-;₂_)) (go (fwd x) c)
  go (fwd (≃𝕊-;₁ x)) front F ∶ c ;₁-    = Π.map _ (Π.map (flip ≃-; refl) front F ∶_;₁-) (go (fwd x) c)
  go (fwd (≃𝕊-;₂ x)) front F ∶ c ;₁-    = _ , ≃-; refl (Eq*.return x) , front F ∶ c ;₁-
  go (fwd (≃𝕊-;₁ x)) (front F ∶ z ;₂ c) = _ , refl , front F ∶ ≃-skips (Eq*.return x) z ;₂ c
  go (fwd (≃𝕊-;₂ x)) (front F ∶ z ;₂ c) = Π.map _ (Π.map₂ (front F ∶ z ;₂_)) (go (fwd x) c)

  go (fwd ≃𝕊-skipˡ) (back B ∶ c ;₁ z)  = contradiction skip (cat-¬skips A c)
  go (fwd ≃𝕊-skipʳ) (back B ∶ c ;₁ z)  = _ , refl , c
  go (fwd ≃𝕊-skipˡ) (back B ∶-;₂ c)    = _ , ≃-skipˡ , c
  go (fwd ≃𝕊-skipʳ) (back B ∶-;₂ c)    = contradiction skip (cat-¬skips A c)
  go (fwd ≃𝕊-skipˡ) front F ∶ c ;₁-    = contradiction skip (cat-¬skips A c)
  go (fwd ≃𝕊-skipʳ) front F ∶ c ;₁-    = _ , ≃-skipʳ , c
  go (fwd ≃𝕊-skipˡ) (front F ∶ z ;₂ c) = _ , refl , c
  go (fwd ≃𝕊-skipʳ) (front F ∶ z ;₂ c) = contradiction skip (cat-¬skips A c)

  go (fwd ≃𝕊-assoc) (back B ∶ here eq ;₁ z) = _ , refl , here (≃-trans eq (≃-; refl (≃-sym (≃-skipsʳ z))))
  go (fwd ≃𝕊-assoc) (back B ∶ back B₁ ∶ c ;₁ z₁ ;₁ z₂) = _ , refl , (back B₁ ∶ c ;₁ (z₁ ; z₂))
  go (fwd ≃𝕊-assoc) (back B ∶ back B₁ ∶-;₂ c ;₁ z) = _ ; _ , refl , (back B₁ ∶-;₂ (back B ∶ c ;₁ z))
  go (fwd ≃𝕊-assoc) (back B ∶ front F ∶ c ;₁-  ;₁ z) = contradiction F B
  go (fwd ≃𝕊-assoc) (back B ∶ front F ∶ x ;₂ c ;₁ z) = contradiction F B
  go (fwd ≃𝕊-assoc) (back B ∶-;₂ c) = _ , ≃-assoc-; , (back B ∶-;₂ (back B ∶-;₂ c))
  go (fwd ≃𝕊-assoc) (front F ∶ here eq ;₁-) with atom-;⁻ A eq
  ... | inj₁ (eq′ , z) = _ , ≃-; refl (≃-sym (≃-skipsˡ z)) , front F ∶ here eq′ ;₁-
  ... | inj₂ (eq′ , z) = _ , refl , front F ∶ z ;₂ front F ∶ here eq′ ;₁-
  go (fwd ≃𝕊-assoc) front F ∶ back B ∶ c ;₁ z ;₁- = contradiction F B
  go (fwd ≃𝕊-assoc) front F ∶ back B ∶-;₂ c ;₁- = contradiction F B
  go (fwd ≃𝕊-assoc) front F ∶ front _ ∶ c ;₁- ;₁- = _ , ≃-assoc-; , front F ∶ c ;₁-
  go (fwd ≃𝕊-assoc) front F ∶ front _ ∶ z ;₂ c ;₁- = _ , refl , (front F ∶ z ;₂ front F ∶ c ;₁-)
  go (fwd ≃𝕊-assoc) (front F ∶ z₁ ; z₂ ;₂ c) = _ , refl , (front F ∶ z₁ ;₂ (front F ∶ z₂ ;₂ c))

  go (fwd ≃𝕊-distr) (back B ∶ here eq ;₁ z) = _ , refl , here (≃-trans eq (≃-brn (≃-sym (≃-skipsʳ z)) (≃-sym (≃-skipsʳ z))))
  go (fwd ≃𝕊-distr) (back B ∶ brn _ c₁ c₂ ;₁ z) = _ , refl , brn B (back B ∶ c₁ ;₁ z) (back B ∶ c₂ ;₁ z)
  go (fwd ≃𝕊-distr) (back B ∶-;₂ c) = _ , ≃-distr , brn B (back B ∶-;₂ c) (back B ∶-;₂ c)
  go (fwd ≃𝕊-distr) front F ∶ here eq ;₁- = contradiction eq (atom≄brn A)
  go (fwd ≃𝕊-distr) front F ∶ brn B c₁ c₂ ;₁- = contradiction F B

  go (bwd (≃𝕊-;₁ x)) (back B ∶ c ;₁ z)  = Π.map _ (Π.map₂ (back B ∶_;₁ z)) (go (bwd x) c)
  go (bwd (≃𝕊-;₂ x)) (back B ∶ c ;₁ z)  = _ , refl , back B ∶ c ;₁ ≃-skips (≃-sym (Eq*.return x)) z
  go (bwd (≃𝕊-;₁ x)) (back B ∶-;₂ c)    = _ , ≃-sym (≃-; (Eq*.return x) refl) , (back B ∶-;₂ c)
  go (bwd (≃𝕊-;₁ x)) front F ∶ c ;₁-    = Π.map _ (Π.map (flip ≃-; refl) front F ∶_;₁-) (go (bwd x) c)
  go (bwd (≃𝕊-;₁ x)) (front F ∶ z ;₂ c) = _ , refl , front F ∶ ≃-skips (≃-sym (Eq*.return x)) z ;₂ c
  go (bwd (≃𝕊-;₂ x)) (back B ∶-;₂ c)    = Π.map _ (Π.map (≃-; refl) (back B ∶-;₂_)) (go (bwd x) c)
  go (bwd (≃𝕊-;₂ x)) front F ∶ c ;₁-    = _ , ≃-sym (≃-; refl (Eq*.return x)) , front F ∶ c ;₁-
  go (bwd (≃𝕊-;₂ x)) (front F ∶ z ;₂ c) = Π.map _ (Π.map₂ (front F ∶ z ;₂_)) (go (bwd x) c)

  go (bwd ≃𝕊-assoc) (back B ∶ c ;₁ (z₁ ; z₂)) = _ , refl , (back B ∶ back B ∶ c ;₁ z₁ ;₁ z₂)
  go (bwd ≃𝕊-assoc) (back B ∶-;₂ here eq) with atom-;⁻ A eq
  ... | inj₁ (eq′ , z) = _ , refl , (back B ∶ back B ∶-;₂ here eq′ ;₁ z)
  ... | inj₂ (eq′ , z) = _ , ≃-; (≃-sym (≃-skipsʳ z)) refl , (back B ∶-;₂ here eq′)
  go (bwd ≃𝕊-assoc) (back B ∶-;₂ (back _ ∶ c ;₁ z)) = _ , refl , (back B ∶ back B ∶-;₂ c ;₁ z)
  go (bwd ≃𝕊-assoc) (back B ∶-;₂ (back _ ∶-;₂ c)) = _ , ≃-sym ≃-assoc-; , (back B ∶-;₂ c)
  go (bwd ≃𝕊-assoc) (back B ∶-;₂ front F ∶ c ;₁-) = contradiction F B
  go (bwd ≃𝕊-assoc) (back B ∶-;₂ (front F ∶ z ;₂ c)) = contradiction F B
  go (bwd ≃𝕊-assoc) front F ∶ c ;₁- = _ , ≃-sym ≃-assoc-; , front F ∶ front F ∶ c ;₁- ;₁-
  go (bwd ≃𝕊-assoc) (front F ∶ z ;₂ here eq) with atom-;⁻ A eq
  ... | inj₁ (eq′ , z′) = _ , ≃-sym (≃-skipsʳ z′) , front F ∶ here (≃-trans eq′ (≃-sym (≃-skipsˡ z))) ;₁-
  ... | inj₂ (eq′ , z′) = _ , refl , front F ∶ z ; z′ ;₂ here eq′
  go (bwd ≃𝕊-assoc) (front F ∶ z ;₂ (back B ∶ c ;₁ _)) = contradiction F B
  go (bwd ≃𝕊-assoc) (front F ∶ z ;₂ (back B ∶-;₂ c)) = contradiction F B
  go (bwd ≃𝕊-assoc) (front F ∶ z ;₂ front _ ∶ c ;₁-) = _ , refl , front F ∶ front F ∶ z ;₂ c ;₁-
  go (bwd ≃𝕊-assoc) (front F ∶ z₁ ;₂ (front _ ∶ z₂ ;₂ c)) = _ , refl , (front F ∶ z₁ ; z₂ ;₂ c)

  go (bwd ≃𝕊-distr) (brn B (here eq₁) (here eq₂)) = {!!}
  go (bwd ≃𝕊-distr) (brn B (here x) (back B₁ ∶ c₂ ;₁ x₁)) = {!!}
  go (bwd ≃𝕊-distr) (brn B (here x) (back B₁ ∶-;₂ c₂)) = {!!}
  go (bwd ≃𝕊-distr) (brn B (here x) front F ∶ c₂ ;₁-) = {!!}
  go (bwd ≃𝕊-distr) (brn B (here x) (front F ∶ x₁ ;₂ c₂)) = {!!}
  go (bwd ≃𝕊-distr) (brn B (back B₁ ∶ c₁ ;₁ x) c₂) = {!!}
  go (bwd ≃𝕊-distr) (brn B (back B₁ ∶-;₂ c₁) c₂) = {!!}
  go (bwd ≃𝕊-distr) (brn B front F ∶ c₁ ;₁- c₂) = {!!}
  go (bwd ≃𝕊-distr) (brn B (front F ∶ x ;₂ c₁) c₂) = {!!}

  go (bwd x) c = {!!}

atom-drop : Atom a → a ⨟ s ≃ s₁ ⨟ s₂ →
  Skips (if front then s₁ else s₂) ⊎ ∃[ s′ ] a ⨟ s′ ≃ s₁ × s ≃ s′ ⨟ s₂
atom-drop A eq = {!!}
