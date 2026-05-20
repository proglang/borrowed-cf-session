{-# OPTIONS --rewriting #-}
module BorrowedCF.Types where

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

pattern _⊗¹_ T U = T ⊗⟨ 𝟙 ⟩ U
pattern _⊗ᴸ_ T U = T ⊗⟨ L ⟩ U

variable
  s s₁ s₂ s₃ s′ : 𝕊 n
  T T₁ T₂ T₃ T′ : 𝕋
  U U₁ U₂ U₃ U′ : 𝕋

data Skips {n} : 𝕊 n → Set where
  skip : Skips skip
  _;_  : (S₁ : Skips s₁) (S₂ : Skips s₂) → Skips (s₁ ; s₂)
  mu   : (S : Skips s) → Skips (mu s)

data Bounded {n} : 𝕊 n → Set where
  `_ : (x : 𝔽 n) → Bounded (` x)
  end  : Bounded (end p)
  ret  : Bounded ret
  _;₁_ : Bounded s₁ → Skips s₂ → Bounded (s₁ ; s₂)
  -;₂_ : Bounded s₂ → Bounded (s₁ ; s₂)
  mu   : Bounded s → Bounded (mu s)
  brn  : Bounded s₁ → Bounded s₂ → Bounded (brn p s₁ s₂)

data Mobile : 𝕋 → Set where
  `⊤  : Mobile `⊤
  arr : Arr.Mobile a → Mobile (T ⟨ a ⟩→ U)
  acq : Bounded s → Mobile ⟨ acq ; s ⟩
  skip : Skips s → Mobile ⟨ s ⟩
  _⊗_ : Mobile T → Mobile U → Mobile (T ⊗⟨ d ⟩ U)

data Unr : 𝕋 → Set where
  `⊤   : Unr `⊤
  _⊗_  : Unr T → Unr U → Unr (T ⊗⟨ d ⟩ U)
  arr  : Arr.Unr a → Unr (T ⟨ a ⟩→ U)
  ⟨_⟩  : Skips s → Unr ⟨ s ⟩

Unr⇒Mobile : Unr T → Mobile T
Unr⇒Mobile `⊤ = `⊤
Unr⇒Mobile (T ⊗ U) = Unr⇒Mobile T ⊗ Unr⇒Mobile U
Unr⇒Mobile (arr {a} U) = arr (Arr.ω⇒M a U)
Unr⇒Mobile ⟨ s ⟩   = skip s

skips? : Un.Decidable (Skips {n})
skips? (` x) = no λ()
skips? (end p) = no λ()
skips? (msg p t) = no λ()
skips? (brn p s₁ s₂) = no λ()
skips? (mu s) = map′ mu (λ{ (mu x) → x }) (skips? s)
skips? (s₁ ; s₂) = map′ (uncurry _;_) (λ{ (x ; y) → (x , y) }) (skips? s₁ ×-dec skips? s₂)
skips? skip = yes skip
skips? ret = no λ()
skips? acq = no λ()

unr? : Un.Decidable Unr
unr? ⟨ s ⟩ = map′ ⟨_⟩ (λ{ ⟨ x ⟩ → x }) (skips? s)
unr? `⊤ = yes `⊤
unr? (t ⟨ a ⟩→ u) with Arr.lin a in eq
... | 𝟙   = no λ{ (arr eq′) → case sym eq ■ eq′ of λ() }
... | unr = yes (arr eq)
unr? (t ⊗⟨ d ⟩ u) = map′ (uncurry _⊗_) (λ{ (unrT ⊗ unrU) → unrT , unrU }) (unr? t ×-dec unr? u)

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

{-# REWRITE dual-involutive #-}

relaxEff : 𝕋 → Eff → 𝕋
relaxEff `⊤ _ = `⊤
relaxEff ⟨ s ⟩ _ = ⟨ s ⟩
relaxEff (t ⟨ a ⟩→ u) e′ = relaxEff t e′ ⟨ record a { eff = e′ } ⟩→ relaxEff u e′
relaxEff (t ⊗⟨ d ⟩ u) e′ = relaxEff t e′ ⊗⟨ d ⟩ relaxEff u e′
