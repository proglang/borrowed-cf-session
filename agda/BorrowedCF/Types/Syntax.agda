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

data Skips {n} : 𝕊 n → Set where
  skip : Skips skip
  _;_  : (S₁ : Skips s₁) (S₂ : Skips s₂) → Skips (s₁ ; s₂)
  mu   : (S : Skips s) → Skips (mu s)

skips-irr : (x y : Skips s) → x ≡ y
skips-irr skip skip = refl
skips-irr (x₁ ; x₂) (y₁ ; y₂) = cong₂ _;_ (skips-irr x₁ y₁) (skips-irr x₂ y₂)
skips-irr (mu x) (mu y) = cong mu (skips-irr x y)

skips? : Un.Decidable (Skips {n})
skips? (` x) = no λ()
skips? (end p) = no λ()
skips? (msg p t) = no λ()
skips? (brn p s₁ s₂) = no λ()
skips? (mu s) = map′ mu (λ{ (mu ss) → ss }) (skips? s)
skips? (s₁ ; s₂) with skips? s₁ | skips? s₂
... | yes ss₁ | yes ss₂ = yes (ss₁ ; ss₂)
... | no ¬ss₁ | _       = no λ{ (ss₁ ; ss₂) → ¬ss₁ ss₁ }
... | yes _   | no ¬ss₂ = no λ{ (ss₁ ; ss₂) → ¬ss₂ ss₂ }
skips? skip = yes skip
skips? ret = no λ()
skips? acq = no λ()
skips? (`` x) = no λ()

¬skips-` : {x : 𝔽 n} → ¬ Skips (` x)
¬skips-` ()

infix 4 𝓖_·_

data 𝓖_·_ (x : 𝔽 n) : 𝕊 n → Set where
  `_  : ∀ {y : 𝔽 n} → x ≢ y → 𝓖 x · ` y
  end : 𝓖 x · end p
  msg : 𝓖 x · msg p T
  brn : 𝓖 x · brn p s₁ s₂
  mu  : 𝓖 suc x · s → 𝓖 x · mu s
  _;- : ¬ Skips s₁ × 𝓖 x · s₁ → 𝓖 x · s₁ ; s₂
  _;_ : Skips s₁ → 𝓖 x · s₂ → 𝓖 x · s₁ ; s₂
  acq : 𝓖 x · acq
  ret : 𝓖 x · ret
  skip : 𝓖 x · skip

  ``_ : (y : ℕ) → 𝓖 x · `` y

𝓖₀ : Pred (𝕊 (1 + n)) _
𝓖₀ = 𝓖 zero ·_

𝓖-irr : {z : 𝔽 n} → (x y : 𝓖 z · s) → x ≡ y
𝓖-irr (` z≢₁) (` z≢₂) = refl
𝓖-irr end end = refl
𝓖-irr msg msg = refl
𝓖-irr brn brn = refl
𝓖-irr (mu x) (mu y) = cong mu (𝓖-irr x y)
𝓖-irr ((_ , x) ;-) ((_ , y) ;-) = cong (λ g → (_ , g) ;-) (𝓖-irr x y)
𝓖-irr ((¬s , _) ;-) (s ; _) = contradiction s ¬s
𝓖-irr (s ; _) ((¬s , _) ;-) = contradiction s ¬s
𝓖-irr (x₁ ; x₂) (y₁ ; y₂) = cong₂ _;_ (skips-irr x₁ y₁) (𝓖-irr x₂ y₂)
𝓖-irr acq acq = refl
𝓖-irr ret ret = refl
𝓖-irr skip skip = refl
𝓖-irr (`` α) (`` α) = refl

infix 4 ⊢_

data ⊢_ : ∀ {κ x} → Ty κ x → Set where
  ⟨_⟩ : ⊢ s → ⊢ ⟨ s ⟩
  `⊤  : ⊢ `⊤
  _`→_ : ⊢ T → ⊢ U → ⊢ T ⟨ a ⟩→ U
  _⊗_ : ⊢ T → ⊢ U → ⊢ T ⊗⟨ d ⟩ U

  `_  : (x : 𝔽 n) → ⊢ ` x
  end : ⊢ end {n} p
  msg : ⊢ T → ⊢ msg {n} p T
  brn : ⊢ s₁ → ⊢ s₂ → ⊢ brn p s₁ s₂
  mu  : 𝓖₀ s → ⊢ s → ⊢ mu s
  _;_ : ⊢ s₁ → ⊢ s₂ → ⊢ s₁ ; s₂
  skip : ⊢ skip {n}
  ret : ⊢ ret {n}
  acq : ⊢ acq {n}

  ``_ : (x : ℕ) → ⊢ ``_ {n} x

⊢-irr : ∀ {κ x} {τ : Ty κ x} (t u : ⊢ τ) → t ≡ u
⊢-irr ⟨ t ⟩ ⟨ u ⟩ = cong ⟨_⟩ (⊢-irr t u)
⊢-irr `⊤ `⊤ = refl
⊢-irr (t₁ `→ t₂) (u₁ `→ u₂) = cong₂ _`→_ (⊢-irr t₁ u₁) (⊢-irr t₂ u₂)
⊢-irr (t₁ ⊗ t₂) (u₁ ⊗ u₂) = cong₂ _⊗_ (⊢-irr t₁ u₁) (⊢-irr t₂ u₂)
⊢-irr (` x) (` x) = refl
⊢-irr end end = refl
⊢-irr (msg t) (msg u) = cong msg (⊢-irr t u)
⊢-irr (brn t₁ t₂) (brn u₁ u₂) = cong₂ brn (⊢-irr t₁ u₁) (⊢-irr t₂ u₂)
⊢-irr (mu x t) (mu y u) = cong₂ mu (𝓖-irr x y) (⊢-irr t u)
⊢-irr (t₁ ; t₂) (u₁ ; u₂) = cong₂ _;_ (⊢-irr t₁ u₁) (⊢-irr t₂ u₂)
⊢-irr skip skip = refl
⊢-irr ret ret = refl
⊢-irr acq acq = refl
⊢-irr (`` α) (`` α) = refl

skips⇒𝓖 : {x : 𝔽 n} → Skips s → 𝓖 x · s
skips⇒𝓖 skip = skip
skips⇒𝓖 (s₁ ; s₂) = s₁ ; skips⇒𝓖 s₂
skips⇒𝓖 (mu s) = mu (skips⇒𝓖 s)

skips⇒⊢ : Skips s → ⊢ s
skips⇒⊢ skip = skip
skips⇒⊢ (s₁ ; s₂) = skips⇒⊢ s₁ ; skips⇒⊢ s₂
skips⇒⊢ (mu s) = mu (skips⇒𝓖 s) (skips⇒⊢ s)

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

μPrefix : ∀ {κ x} → Ty κ x → ℕ
μPrefix (mu t)  = 1 + μPrefix t
μPrefix _       = 0
