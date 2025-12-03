module BorrowedCF.Substitution where

open import BorrowedCF.Prelude

open Nat.Variables

variable
  α α₁ α₂ α₃ α′ : 𝔽 n

data Const : Set where
  ⟨⟩ `new `fork
     `close `wait
     `send `recv
     `lsplit `rsplit
     `drop `acquire
       : Const

infix 9 `_

data Tm n : Set where
  K   : Const → Tm n
  `_  : (α : 𝔽 n) → Tm n
  `λ  : (e : Tm (1 + n)) → Tm n
  _·_ : (e₁ e₂ : Tm n) → Tm n
  _;_ : (e₁ e₂ : Tm n) → Tm n
  _⊗_ : (e₁ e₂ : Tm n) → Tm n
  let-⊗ : (e₁ : Tm n) (e₂ : Tm (2 + n)) → Tm n
  `inl `inr : (e : Tm n) → Tm n
  `case_of[_,_] : (e : Tm n) (e₁ e₂ : Tm (1 + n)) → Tm n

data Dir : Set where
  ‼ ⁇ : Dir

data Mode : Set where
  owned borrowed : Mode

data Mobility : Set where
  mobile static : Mobility

data Direction : Set where
  L R 𝟙 : Direction

data Effect : Set where
  ℙ 𝕀 : Effect

data Ty : Set

data 𝕊 n : Set where
  ε : 𝕊 n
  _;_ : (s₁ s₂ : 𝕊 n) → 𝕊 n
  end : (⁉ : Dir) (m : Mode) → 𝕊 n
  msg : (⁉ : Dir) (t : Ty) → 𝕊 n
  branch : (⁉ : Dir) (s₁ s₂ : 𝕊 n) → 𝕊 n
  `_  : (α : 𝔽 n) → 𝕊 n
  μ   : (s : 𝕊 (1 + n)) → 𝕊 n

data Ty where
  `⊤ : Ty
  arr : (m : Mobility) (d : Direction) (ℯ : Effect) (t₁ t₂ : Ty) → Ty
  _`+_ : (t₁ t₂ : Ty) → Ty
  S  : (s : 𝕊 0) → Ty

Ctxt = Vec Ty

private variable
  e e₁ e₂ e₃ e′ : Tm n
  t t₁ t₂ t₃ t′ : Ty
  s s₁ s₂ s₃ s′ : 𝕊 n
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctxt n

infix 4 _⊢_∶_ _∋_∶_

_∋_∶_ : Ctxt n → 𝔽 n → Ty → Set
Γ ∋ α ∶ t = lookup Γ α ≡ t

data _⊢_∶_ (Γ : Vec Ty n) : Tm n → Ty → Set where
  ⊢` :
    Γ ∋ α ∶ t →
    -----------
    Γ ⊢ ` α ∶ t
