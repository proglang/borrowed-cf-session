{-# OPTIONS --rewriting #-}
module BorrowedCF.Types.Syntax where

open import BorrowedCF.Prelude

open Nat.Variables

data Pol : Set where
  ‼ ⁇ : Pol

data Dir : Set where
  L R 𝟙 : Dir

data Mob : Set where
  M S : Mob

data Eff : Set where
  ℙ 𝕀 : Eff

variable ϵ ϵ₁ ϵ₂ ϵ₃ ϵ′ : Eff

data _≤ϵ_ : Rel Eff 0ℓ where
  ℙ≤ϵ : ℙ ≤ϵ ϵ
  𝕀≤𝕀 : 𝕀 ≤ϵ 𝕀

≤ϵ-refl : ϵ ≤ϵ ϵ
≤ϵ-refl {ℙ} = ℙ≤ϵ
≤ϵ-refl {𝕀} = 𝕀≤𝕀

≤ϵ-trans : ϵ₁ ≤ϵ ϵ₂ → ϵ₂ ≤ϵ ϵ₃ → ϵ₁ ≤ϵ ϵ₃
≤ϵ-trans ℙ≤ϵ ≤₂₃ = ℙ≤ϵ
≤ϵ-trans 𝕀≤𝕀 ≤₂₃ = ≤₂₃

data Lin : Set where
  𝟙 unr : Lin

record Arr : Set where
  constructor arr
  field
    lin : Lin
    dir : Dir
    mob : Mob
    eff : Eff

  Mobile = mob ≡ M
  Unr = lin ≡ unr
  Par = dir ≡ 𝟙

  field
    ω⇒M : Unr → Mobile
    ω⇒𝟙 : Unr → Par

data Kind : Set where
  𝕤 𝕥 : Kind

variable
  a a₁ a₂ a₃ a′ : Arr
  p p₁ p₂ p₃ p′ : Pol
  d d₁ d₂ d₃ d′ : Dir
  𝓂 𝓂₁ 𝓂₂ 𝓂₃ 𝓂′ : Mob
  κ κ₁ κ₂ κ₃ κ′ : Kind

⟦_⟧κ : Kind → Set
⟦ 𝕤 ⟧κ = ℕ
⟦ 𝕥 ⟧κ = ⊤

data Ty : ∀ κ → ⟦ κ ⟧κ → Set

𝕊 = Ty 𝕤
𝕋 = Ty 𝕥 _

infixl 17 _;_
infixl 16 _⊗⟨_⟩_ _⊗¹_ _⊗ᴸ_
infixr 15 _⟨_⟩→_

data Ty where
  ⟨_⟩    : (s : 𝕊 0) → 𝕋
  `⊤     : 𝕋
  _⟨_⟩→_ : (t : 𝕋) (a : Arr) (u : 𝕋) → 𝕋
  _⊗⟨_⟩_ : (t : 𝕋) (d : Dir) (u : 𝕋) → 𝕋

  `_  : (x : 𝔽 n) → 𝕊 n
  end : (p : Pol) → 𝕊 n
  msg : (p : Pol) (t : 𝕋) → 𝕊 n
  brn : (p : Pol) (s₁ s₂ : 𝕊 n) → 𝕊 n
  mu  : (s : 𝕊 (suc n)) → 𝕊 n
  _;_ : (s₁ s₂ : 𝕊 n) → 𝕊 n
  skip ret acq : 𝕊 n

  -- Unification variables
  ``_ : (x : ℕ) → 𝕊 n

pattern _⊗¹_ T U = T ⊗⟨ 𝟙 ⟩ U
pattern _⊗ᴸ_ T U = T ⊗⟨ L ⟩ U

infixr 15 _→1M_∣_

_→1M_∣_ : 𝕋 → 𝕋 → Eff → 𝕋
_→1M_∣_ T U e = T ⟨ arr unr 𝟙 M e (λ _ → refl) (λ _ → refl) ⟩→ U

variable
  s s₁ s₂ s₃ s′ s₁′ s₂′ : 𝕊 n
  T T₁ T₂ T₃ T′ : 𝕋
  U U₁ U₂ U₃ U′ : 𝕋

dualPol : Pol → Pol
dualPol ‼ = ⁇
dualPol ⁇ = ‼

dual : 𝕊 n → 𝕊 n
dual (` x) = ` x
dual (end p) = end (dualPol p)
dual (msg p t) = msg (dualPol p) t
dual (brn p s₁ s₂) = brn (dualPol p) (dual s₁) (dual s₂)
dual (mu s) = mu (dual s)
dual (s₁ ; s₂) = dual s₁ ; dual s₂
dual skip = skip
dual ret = ret
dual acq = acq
dual (`` x) = `` x

dualPol-involutive : dualPol ∘ dualPol ≗ id
dualPol-involutive ‼ = refl
dualPol-involutive ⁇ = refl

{-# REWRITE dualPol-involutive #-}

dual-involutive : dual {n} ∘ dual ≗ id
dual-involutive (` x) = refl
dual-involutive (end p) = refl
dual-involutive (msg p t) = refl
dual-involutive (brn p s₁ s₂) = cong₂ (brn p) (dual-involutive s₁) (dual-involutive s₂)
dual-involutive (mu s) = cong mu (dual-involutive s)
dual-involutive (s₁ ; s₂) = cong₂ _;_ (dual-involutive s₁) (dual-involutive s₂)
dual-involutive skip = refl
dual-involutive ret = refl
dual-involutive acq = refl
dual-involutive (`` x) = refl

{-# REWRITE dual-involutive #-}

module Sub where
  open import BorrowedCF.FinKits as Kits hiding (Syntax) public

  open module Syntax = Kits.Syntax record
    { Tm = 𝕊
    ; `_ = `_
    ; `-injective = λ{ refl → refl }
    }
    hiding (Traversal; Tm; `_)
    renaming (id to idₖ)
    public

  infixl 5 _⋯_

  _⋯_ : ⦃ K : Kit 𝓕 ⦄ → 𝕊 m → m –[ K ]→ n → 𝕊 n
  (` x) ⋯ ϕ = `/id (ϕ x)
  end p ⋯ ϕ = end p
  msg p t ⋯ ϕ = msg p t
  brn p s₁ s₂ ⋯ ϕ = brn p (s₁ ⋯ ϕ) (s₂ ⋯ ϕ)
  mu s ⋯ ϕ = mu (s ⋯ ϕ ↑)
  (s₁ ; s₂) ⋯ ϕ = (s₁ ⋯ ϕ) ; (s₂ ⋯ ϕ) 
  skip ⋯ ϕ = skip
  ret ⋯ ϕ = ret
  acq ⋯ ϕ = acq
  (`` x) ⋯ ϕ = `` x

  ⋯-id : ⦃ K : Kit 𝓕 ⦄ (s : 𝕊 n) {ϕ : n –[ K ]→ n} → ϕ ≗ idₖ → s ⋯ ϕ ≡ s
  ⋯-id (` x) eq = cong `/id (eq x) ■ `/`-is-` x
  ⋯-id (end p) eq = refl
  ⋯-id (msg p t) eq = refl
  ⋯-id (brn p s₁ s₂) eq = cong₂ (brn p) (⋯-id s₁ eq) (⋯-id s₂ eq)
  ⋯-id (mu s) eq = cong mu (⋯-id s (id↑ eq))
  ⋯-id (s₁ ; s₂) eq = cong₂ _;_ (⋯-id s₁ eq) (⋯-id s₂ eq)
  ⋯-id skip eq = refl
  ⋯-id ret eq = refl
  ⋯-id acq eq = refl
  ⋯-id (`` x) eq = refl

  ⋯-cong : ⦃ K : Kit 𝓕 ⦄ (s : 𝕊 m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → s ⋯ ϕ₁ ≡ s ⋯ ϕ₂
  ⋯-cong (` x) eq = cong `/id (eq x)
  ⋯-cong (end p) eq = refl
  ⋯-cong (msg p t) eq = refl
  ⋯-cong (brn p s₁ s₂) eq = cong₂ (brn p) (⋯-cong s₁ eq) (⋯-cong s₂ eq)
  ⋯-cong (mu s) eq = cong mu (⋯-cong s (eq ~↑))
  ⋯-cong (s₁ ; s₂) eq = cong₂ _;_ (⋯-cong s₁ eq) (⋯-cong s₂ eq)
  ⋯-cong skip eq = refl
  ⋯-cong ret eq = refl
  ⋯-cong acq eq = refl
  ⋯-cong (`` x) eq = refl

  open module Traversal = Syntax.Traversal record
    { _⋯_ = _⋯_
    ; ⋯-var = λ x ϕ → refl
    ; ⋯-id = ⋯-id
    ; ⋯-cong = ⋯-cong
    }
    hiding (_⋯_; ⋯-id; ⋯-cong; CTraversal)
    public

  fusion :
    ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
    (s : 𝕊 n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) → s ⋯ ϕ₁ ⋯ ϕ₂ ≡ s ⋯ ϕ₁ ·ₖ ϕ₂
  fusion (` x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ x) ϕ₂)
  fusion (end p) ϕ₁ ϕ₂ = refl
  fusion (msg p t) ϕ₁ ϕ₂ = refl
  fusion (brn p s₁ s₂) ϕ₁ ϕ₂ = cong₂ (brn p) (fusion s₁ ϕ₁ ϕ₂) (fusion s₂ ϕ₁ ϕ₂)
  fusion (mu s) ϕ₁ ϕ₂ = cong mu $
    fusion s (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong s (sym ∘ dist-↑-· ϕ₁ ϕ₂)
  fusion (s₁ ; s₂) ϕ₁ ϕ₂ = cong₂ _;_ (fusion s₁ ϕ₁ ϕ₂) (fusion s₂ ϕ₁ ϕ₂)
  fusion skip ϕ₁ ϕ₂ = refl
  fusion ret ϕ₁ ϕ₂ = refl
  fusion acq ϕ₁ ϕ₂ = refl
  fusion (`` x) ϕ₁ ϕ₂ = refl

  open module CTraversal = Traversal.CTraversal record { fusion = fusion }
    hiding (fusion)
    public


-- relaxEff : 𝕋 → Eff → 𝕋
-- relaxEff `⊤ _ = `⊤
-- relaxEff ⟨ s ⟩ _ = ⟨ s ⟩
-- relaxEff (t ⟨ a ⟩→ u) e′ = relaxEff t e′ ⟨ record a { eff = e′ } ⟩→ relaxEff u e′
-- relaxEff (t ⊗⟨ d ⟩ u) e′ = relaxEff t e′ ⊗⟨ d ⟩ relaxEff u e′
