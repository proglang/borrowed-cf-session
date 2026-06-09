{-# OPTIONS --rewriting #-}

module BorrowedCF.Context.Base where

open import BorrowedCF.Prelude
open import BorrowedCF.Types hiding (s; s₁; s₂; s₃; s′)

open Nat.Variables

import Data.Vec.Functional
open Data.Vec.Functional using (Vector)
open Data.Vec.Functional using () renaming (_∷_ to _⸴_) public

Ctx = Vector 𝕋

variable
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctx n

data ParSeq : Set where
  par seq : ParSeq

infixl 17 _∥_ _;_

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
open Un

module _ {ℓ} (P : Pred 𝕋 ℓ) (Γ : Ctx n) where
  data AllCx : Struct n → Set ℓ where
    []  : AllCx []
    _∥_ : AllCx α → AllCx β → AllCx (α ∥ β)
    _;_ : AllCx α → AllCx β → AllCx (α ; β)
    `_  : ∀ {x} → P (Γ x) → AllCx (` x)

allCx-≗ : ∀ {ℓ} {P : Pred 𝕋 ℓ} → Γ ≗ Γ′ → AllCx P Γ γ → AllCx P Γ′ γ
allCx-≗ eq [] = []
allCx-≗ eq (x ∥ y) = allCx-≗ eq x ∥ allCx-≗ eq y
allCx-≗ eq (x ; y) = allCx-≗ eq x ; allCx-≗ eq y
allCx-≗ eq (`_ {x} px) rewrite eq x = ` px

module _ {ℓ} {P : Pred 𝕋 ℓ} {Γ : Ctx n} where
  allCx-∥⁻¹ : AllCx P Γ (α ∥ β) → AllCx P Γ α × AllCx P Γ β
  allCx-∥⁻¹ (x ∥ y) = x , y

  allCx-;⁻¹ : AllCx P Γ (α ; β) → AllCx P Γ α × AllCx P Γ β
  allCx-;⁻¹ (x ; y) = x , y

  allCx? : Decidable P → Decidable (AllCx P Γ)
  allCx? P? (` x) = map′ `_ (λ{ (` Px) → Px }) (P? (Γ x))
  allCx? P? [] = yes []
  allCx? P? (α ∥ β) = map′ (uncurry _∥_) allCx-∥⁻¹ (allCx? P? α ×-dec allCx? P? β)
  allCx? P? (α ; β) = map′ (uncurry _;_) allCx-;⁻¹ (allCx? P? α ×-dec allCx? P? β)

module _ {p q} {P : Pred 𝕋 p} {Q : Pred 𝕋 q} where
  allCx-map : (P ⊆ Q) → AllCx P Γ ⊆ AllCx Q Γ
  allCx-map f [] = []
  allCx-map f (x ∥ y) = allCx-map f x ∥ allCx-map f y
  allCx-map f (x ; y) = allCx-map f x ; allCx-map f y
  allCx-map f (` x) = ` f x

UnrCx : REL (Ctx n) (Struct n) _
UnrCx = AllCx Unr

MobCx : REL (Ctx n) (Struct n) _
MobCx = AllCx Mobile

unrCx? : Un.Decidable (UnrCx Γ)
unrCx? = allCx? unr?

UnrCx⇒MobCx : UnrCx Γ ⊆ MobCx Γ
UnrCx⇒MobCx = allCx-map unr⇒mobile
