module BorrowedCF.Context where

open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Modes
open import BorrowedCF.Types hiding (s; s₁; s₂; s₃; s′)
open import BorrowedCF.Renaming

open Nat.Variables

data ParSeq : Set where
  par seq : ParSeq

infix 12 _∥_ _;_

data Struct (n : ℕ) : Set where
  `_  : 𝔽 n → Struct n
  []  : Struct n
  _∥_ : Struct n → Struct n → Struct n
  _;_ : Struct n → Struct n → Struct n

private variable
  α α₁ α₂ α₃ α′ : Struct n
  β β₁ β₂ β₃ β′ : Struct n

variable
  γ γ₁ γ₂ γ₃ γ′ : Struct n

infix 4 _≈′_

data _≈′_ {n} : Rel (Struct n) 0ℓ where
  ;′-unit  : α ; [] ≈′ α
  ;′-assoc : (α ; β) ; γ ≈′ α ; (β ; γ)
  ;′-cong₁ : α ≈′ α′ → α ; β ≈′ α′ ; β
  ;′-cong₂ : β ≈′ β′ → α ; β ≈′ α ; β′

  ∥′-unit  : α ∥ [] ≈′ α
  ∥′-assoc : (α ∥ β) ∥ γ ≈′ α ∥ (β ∥ γ)
  ∥′-comm  : α ∥ β ≈′ β ∥ α
  ∥′-cong₁ : α ≈′ α′ → α ∥ β ≈′ α′ ∥ β

infix 4 _≈_

_≈_ : Rel (Struct n) _
_≈_ = EqClosure _≈′_

;-unit : α ; [] ≈ α
;-unit = Eq*.return ;′-unit

;-assoc : (α ; β) ; γ ≈ α ; (β ; γ)
;-assoc = Eq*.return ;′-assoc

;-cong : α ≈ α′ → β ≈ β′ → α ; β ≈ α′ ; β′
;-cong xs ys = Eq*.gmap (_; _) ;′-cong₁ xs ◅◅ Eq*.gmap (_ ;_) ;′-cong₂ ys

∥-unit : α ∥ [] ≈ α
∥-unit = Eq*.return ∥′-unit

∥-assoc : (α ∥ β) ∥ γ ≈ α ∥ (β ∥ γ)
∥-assoc = Eq*.return ∥′-assoc

∥-comm : α ∥ β ≈ β ∥ α
∥-comm = Eq*.return ∥′-comm

∥-cong : α ≈ α′ → β ≈ β′ → α ∥ β ≈ α′ ∥ β′
∥-cong xs ys = Eq*.gmap (_∥ _) ∥′-cong₁ xs ◅◅ ∥-comm ◅◅ Eq*.gmap (_∥ _) ∥′-cong₁ ys ◅◅ ∥-comm
