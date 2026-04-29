module BorrowedCF.Context.Base where

open import Data.Vec.Functional using (Vector)

open import BorrowedCF.Prelude
open import BorrowedCF.Types hiding (s; s₁; s₂; s₃; s′)

open Nat.Variables

Ctx = Vector 𝕋

variable
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctx n

data ParSeq : Set where
  par seq : ParSeq

infix 12 _∥_ _;_

data Struct (n : ℕ) : Set where
  `_  : 𝔽 n → Struct n
  []  : Struct n
  _∥_ : Struct n → Struct n → Struct n
  _;_ : Struct n → Struct n → Struct n

variable
  γ γ₁ γ₂ γ₃ γ′ : Struct n

module Variables where
  variable
    α α₁ α₂ α₃ α′ α₁′ α₂′ : Struct n
    β β₁ β₂ β₃ β′ β₁′ β₂′ : Struct n

open Variables

module _ {ℓ} (P : Pred 𝕋 ℓ) (Γ : Ctx n) where
  data AllCx : Struct n → Set ℓ where
    []  : AllCx []
    _∥_ : AllCx α → AllCx β → AllCx (α ∥ β)
    _;_ : AllCx α → AllCx β → AllCx (α ; β)
    `_  : ∀ {x} → P (Γ x) → AllCx (` x)

UnrCx : REL (Ctx n) (Struct n) _
UnrCx = AllCx Unr

MobCx : REL (Ctx n) (Struct n) _
MobCx = AllCx Mobile
