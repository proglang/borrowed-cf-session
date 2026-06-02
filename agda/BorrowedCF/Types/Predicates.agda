{-# OPTIONS --rewriting #-}
module BorrowedCF.Types.Predicates where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Syntax

open Un hiding (U)
open Bin using (_Respects_)
open Nat.Variables

data Bounded {n} : 𝕊 n → Set where
  `_ : (x : 𝔽 n) → Bounded (` x)
  end  : Bounded (end p)
  ret  : Bounded ret
  _;₁_ : Bounded s₁ → Skips s₂ → Bounded (s₁ ; s₂)
  -;₂_ : Bounded s₂ → Bounded (s₁ ; s₂)
  mu   : Bounded s → Bounded (mu s)
  brn  : Bounded s₁ → Bounded s₂ → Bounded (brn p s₁ s₂)

skips⊥bounded : Skips s → Bounded s → ⊥
skips⊥bounded skip ()
skips⊥bounded (s₁ ; s₂) (b ;₁ x) = skips⊥bounded s₁ b
skips⊥bounded (s₁ ; s₂) (-;₂ b) = skips⊥bounded s₂ b
skips⊥bounded (mu s) (mu b) = skips⊥bounded s b

bounded-⋯ᵣ : {ρ : m →ᵣ n} → Bounded s → Bounded (s ⋯ ρ)
bounded-⋯ᵣ (` x) = ` _
bounded-⋯ᵣ end = end
bounded-⋯ᵣ ret = ret
bounded-⋯ᵣ (b ;₁ x) = bounded-⋯ᵣ b ;₁ skips-⋯ x
bounded-⋯ᵣ (-;₂ b) = -;₂ bounded-⋯ᵣ b
bounded-⋯ᵣ (mu b) = mu (bounded-⋯ᵣ b)
bounded-⋯ᵣ (brn b b₁) = brn (bounded-⋯ᵣ b) (bounded-⋯ᵣ b₁)

bounded-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → Bounded s → (∀ x → Bounded (`/id (ϕ x))) → Bounded (s ⋯ ϕ)
bounded-⋯ (` x) ∀B = ∀B x
bounded-⋯ end ∀B = end
bounded-⋯ ret ∀B = ret
bounded-⋯ (b ;₁ x) ∀B = (bounded-⋯ b ∀B) ;₁ (skips-⋯ x)
bounded-⋯ (-;₂ b) ∀B = -;₂ bounded-⋯ b ∀B
bounded-⋯ ⦃ K ⦄ (mu b) ∀B = mu (bounded-⋯ b λ where
  zero → subst Bounded (sym (`/`-is-` ⦃ K ⦄ _)) (` zero)
  (suc x) → subst Bounded (wk-`/id _) (bounded-⋯ᵣ (∀B x)))
bounded-⋯ (brn b b₁) ∀B = brn (bounded-⋯ b ∀B) (bounded-⋯ b₁ ∀B)

bounded-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → Bounded (s ⋯ ϕ) → (∀ z → ¬ Skips (`/id (ϕ z))) → Bounded s
bounded-⋯⁻¹ {s = ` x} b ∀¬S = ` x
bounded-⋯⁻¹ {s = end p} b ∀¬S = end
bounded-⋯⁻¹ {s = brn p s₁ s₂} (brn b₁ b₂) ∀¬S = brn (bounded-⋯⁻¹ b₁ ∀¬S) (bounded-⋯⁻¹ b₂ ∀¬S)
bounded-⋯⁻¹ {s = mu s} ⦃ K ⦄ (mu b) ∀¬S = Bounded.mu $ bounded-⋯⁻¹ b λ where
  zero → ¬skips-`/` K
  (suc x) → ∀¬S x ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id _))
bounded-⋯⁻¹ {s = s₁ ; s₂} (b ;₁ x) ∀¬S = (bounded-⋯⁻¹ b ∀¬S) ;₁ skips-⋯⁻¹ x ∀¬S
bounded-⋯⁻¹ {s = s₁ ; s₂} (-;₂ b) ∀¬S = -;₂ (bounded-⋯⁻¹ b ∀¬S)
bounded-⋯⁻¹ {s = ret} b ∀¬S = ret

≃-bounded : Bounded {n} Respects _≃_
≃-bounded refl = id
≃-bounded (x ◅ xs) = ≃-bounded xs ∘ go x where
  go : SymClosure _≃𝕊_ s₁ s₂ → Bounded s₁ → Bounded s₂
  go (fwd ≃𝕊-μ) (mu b) = bounded-⋯ b λ where
    zero → mu b
    (suc x) → ` x
  go (fwd (≃𝕊-;₁ x)) (b ;₁ x₁) = go (fwd x) b ;₁ x₁
  go (fwd (≃𝕊-;₁ x)) (-;₂ b) = -;₂ b
  go (fwd (≃𝕊-;₂ x)) (b ;₁ x₁) = b ;₁ ≃-skips (Eq*.return x) x₁
  go (fwd (≃𝕊-;₂ x)) (-;₂ b) = -;₂ go (fwd x) b
  go (fwd ≃𝕊-skipˡ) (-;₂ b) = b
  go (fwd ≃𝕊-skipʳ) (b ;₁ x) = b
  go (fwd ≃𝕊-skipˡ) (() ;₁ _)
  go (fwd ≃𝕊-skipʳ) (-;₂ ())
  go (fwd ≃𝕊-assoc) ((b ;₁ x₁) ;₁ x) = b ;₁ (x₁ ; x)
  go (fwd ≃𝕊-assoc) ((-;₂ b) ;₁ x) = -;₂ (b ;₁ x)
  go (fwd ≃𝕊-assoc) (-;₂ b) = -;₂ (-;₂ b)
  go (fwd ≃𝕊-distr) (brn b b₁ ;₁ x) = brn (b ;₁ x) (b₁ ;₁ x)
  go (fwd ≃𝕊-distr) (-;₂ b) = brn (-;₂ b) (-;₂ b)
  go (bwd (≃𝕊-;₁ x)) (b ;₁ x₁) = go (bwd x) b ;₁ x₁
  go (bwd (≃𝕊-;₁ x)) (-;₂ b) = -;₂ b
  go (bwd (≃𝕊-;₂ x)) (b ;₁ x₁) = b ;₁ ≃-skips (Star.return (bwd x)) x₁
  go (bwd (≃𝕊-;₂ x)) (-;₂ b) = -;₂ go (bwd x) b
  go (bwd ≃𝕊-μ) b = Bounded.mu $ bounded-⋯⁻¹ b λ where
    zero (mu s) → skips⊥bounded (skips-⋯ s) b
    (suc x) ()
  go (bwd ≃𝕊-skipˡ) b = -;₂ b
  go (bwd ≃𝕊-skipʳ) b = b ;₁ skip
  go (bwd ≃𝕊-assoc) (b ;₁ (x ; x₁)) = (b ;₁ x) ;₁ x₁
  go (bwd ≃𝕊-assoc) (-;₂ (b ;₁ x)) = (-;₂ b) ;₁ x
  go (bwd ≃𝕊-assoc) (-;₂ (-;₂ b)) = -;₂ b
  go (bwd ≃𝕊-distr) (brn (b ;₁ x) (b₁ ;₁ x₁)) = brn b b₁ ;₁ x₁
  go (bwd ≃𝕊-distr) (brn (b ;₁ x) (-;₂ b₁)) = -;₂ b₁
  go (bwd ≃𝕊-distr) (brn (-;₂ b) b₁) = -;₂ b

module _ (PA : Arr → Set) (PS : 𝕊 0 → Set) where
  data TPred : 𝕋 → Set where
    `⊤  : TPred `⊤
    arr : PA a → TPred (T ⟨ a ⟩→ U)
    _⊗_ : TPred T → TPred U → TPred (T ⊗⟨ d ⟩ U)
    _⊕_ : TPred T → TPred U → TPred (T ⊕ U)
    ⟨_⟩ : PS s → TPred ⟨ s ⟩

tpred-≃ : {PA : Arr → Set} {PS : 𝕊 0 → Set} → PS Respects _≃_ → TPred PA PS Respects _≃_
tpred-≃ ps≃ `⊤ `⊤ = `⊤
tpred-≃ ps≃ (eq₁ ⊗ eq₂) (px ⊗ py) = tpred-≃ ps≃ eq₁ px ⊗ tpred-≃ ps≃ eq₂ py
tpred-≃ ps≃ (eq₁ ⊕ eq₂) (px ⊕ py) = tpred-≃ ps≃ eq₁ px ⊕ tpred-≃ ps≃ eq₂ py
tpred-≃ ps≃ (eq₁ `→ eq₂) (arr pa) = arr pa
tpred-≃ ps≃ ⟨ eq ⟩ ⟨ ps ⟩ = ⟨ ps≃ eq ps ⟩

tpred-map : {PA₁ PA₂ : Arr → Set} {PS₁ PS₂ : 𝕊 0 → Set} → PA₁ ⊆ PA₂ → PS₁ ⊆ PS₂ → TPred PA₁ PS₁ ⊆ TPred PA₂ PS₂
tpred-map pa⊆ ps⊆ `⊤ = `⊤
tpred-map pa⊆ ps⊆ (arr pa) = arr (pa⊆ pa)
tpred-map pa⊆ ps⊆ (px ⊗ py) = tpred-map pa⊆ ps⊆ px ⊗ tpred-map pa⊆ ps⊆ py
tpred-map pa⊆ ps⊆ (px ⊕ py) = tpred-map pa⊆ ps⊆ px ⊕ tpred-map pa⊆ ps⊆ py
tpred-map pa⊆ ps⊆ ⟨ s ⟩ = ⟨ ps⊆ s ⟩

tpred? : {PA : Arr → Set} {PS : 𝕊 0 → Set} → Decidable PA → Decidable PS → Decidable (TPred PA PS)
tpred? pa? ps? ⟨ s ⟩ = map′ ⟨_⟩ (λ{ ⟨ ps ⟩ → ps }) (ps? s)
tpred? pa? ps? `⊤ = yes `⊤
tpred? pa? ps? (t ⟨ a ⟩→ u) = map′ arr (λ{ (arr pa) → pa }) (pa? a)
tpred? pa? ps? (t ⊗⟨ d ⟩ u) = map′ (uncurry _⊗_) (λ{ (pt ⊗ pu) → pt , pu }) (tpred? pa? ps? t ×-dec tpred? pa? ps? u)
tpred? pa? ps? (t ⊕ u) = map′ (uncurry _⊕_) (λ{ (pt ⊕ pu) → pt , pu }) (tpred? pa? ps? t ×-dec tpred? pa? ps? u)

Mobile = TPred Arr.Mobile (Skips ∪ λ s → ∃[ s′ ] Bounded s′ × s ≃ acq ; s′)

Unr = TPred Arr.Unr Skips

unr⇒mobile : Unr ⊆ Mobile
unr⇒mobile = tpred-map (λ {a} → Arr.ω⇒M a) inj₁

mobile-≃ : Mobile Respects _≃_
mobile-≃ = tpred-≃ λ eq → Sum.map (≃-skips eq) (Π.map₂ (Π.map₂ (≃-trans (≃-sym eq))))

unr-≃ : Unr Respects _≃_
unr-≃ = tpred-≃ ≃-skips

unr? : Un.Decidable Unr
unr? = tpred? lin? skips?
  where lin? : ∀ a → Dec (Arr.Unr a)
        lin? a with Arr.lin a
        ... | 𝟙 = no λ()
        ... | unr = yes refl
