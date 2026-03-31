module BorrowedCF.Types where

open import BorrowedCF.Prelude

data Pol : Set where
  ‼ ⁇ : Pol

data Dir : Set where
  L R 𝟙 : Dir

data Mob : Set where
  mob loc : Mob

data Eff : Set where
  ℙ 𝕀 : Eff

variable
  p p₁ p₂ p₃ p′ : Pol
  d d₁ d₂ d₃ d′ : Dir
  𝓂 𝓂₁ 𝓂₂ 𝓂₃ 𝓂′ : Mob
  ϵ ϵ₁ ϵ₂ ϵ₃ ϵ′ : Eff

data 𝕊 (n : ℕ) : Set

data 𝕋 : Set where
  ⟨_⟩  : (s : 𝕊 0) → 𝕋
  unit : 𝕋
  arr  : (m : Mob) (d : Dir) (e : Eff) (t u : 𝕋) → 𝕋
  pair : (d : Dir) (t u : 𝕋) → 𝕋

data 𝕊 n where
  end : (p : Pol) → 𝕊 n
  msg : (p : Pol) (t : 𝕋) → 𝕊 n
  brn : (p : Pol) (s₁ s₂ : 𝕊 n) → 𝕊 n
  mu  : (s : 𝕊 (suc n)) → 𝕊 n
  _;_ : (s₁ s₂ : 𝕊 n) → 𝕊 n
  skip ret acq : 𝕊 n
