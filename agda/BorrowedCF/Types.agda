module BorrowedCF.Types where

open import BorrowedCF.Prelude

open Nat.Variables

data Pol : Set where
  ‼ ⁇ : Pol

data Dir : Set where
  L R 𝟙 : Dir

data Mob : Set where
  mob loc : Mob

data Eff : Set where
  ℙ 𝕀 : Eff

data Kind : Set where
  𝕤 𝕥 : Kind

variable
  p p₁ p₂ p₃ p′ : Pol
  d d₁ d₂ d₃ d′ : Dir
  𝓂 𝓂₁ 𝓂₂ 𝓂₃ 𝓂′ : Mob
  ϵ ϵ₁ ϵ₂ ϵ₃ ϵ′ : Eff
  κ κ₁ κ₂ κ₃ κ′ : Kind

⟦_⟧κ : Kind → Set
⟦ 𝕤 ⟧κ = ℕ
⟦ 𝕥 ⟧κ = ⊤

data Ty : ∀ κ → ⟦ κ ⟧κ → Set

𝕊 = Ty 𝕤
𝕋 = Ty 𝕥 _

data Ty where
  ⟨_⟩  : 𝕊 0 → 𝕋
  unit : 𝕋
  arr  : (m : Mob) (d : Dir) (e : Eff) (t u : 𝕋) → 𝕋
  pair : (d : Dir) (t u : 𝕋) → 𝕋

  `_  : (x : 𝔽 n) → 𝕊 n
  end : (p : Pol) → 𝕊 n
  msg : (p : Pol) (t : 𝕋) → 𝕊 n
  brn : (p : Pol) (s₁ s₂ : 𝕊 n) → 𝕊 n
  mu  : (s : 𝕊 (suc n)) → 𝕊 n
  _;_ : (s₁ s₂ : 𝕊 n) → 𝕊 n
  skip ret acq : 𝕊 n

variable
  s s₁ s₂ s₃ s′ : 𝕊 n

postulate
  Skips : 𝕊 n → Set

data Bounded {n} : 𝕊 n → Set where
  `_ : (x : 𝔽 n) → Bounded (` x)
  end : Bounded (end p)
  ret : Bounded ret
  _;₁_ : Bounded s₁ → Skips s₂ → Bounded (s₁ ; s₂)
  -;₂_ : Bounded s₂ → Bounded (s₁ ; s₂)
  mu   : Bounded s → Bounded (mu s)
  brn  : Bounded s₁ → Bounded s₂ → Bounded (brn p s₁ s₂)

data Mobile : 𝕋 → Set where
  unit : Mobile unit
  arr  : ∀ {t u} → Mobile (arr mob d ϵ t u)
  acq  : Bounded s → Mobile ⟨ acq ; s ⟩
  pair : ∀ {t u} → Mobile t → Mobile u → Mobile (pair d t u)

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
