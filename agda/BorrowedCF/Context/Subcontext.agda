module BorrowedCF.Context.Subcontext where

import Relation.Binary.Reasoning.Preorder as PreorderReasoning

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence

open Nat.Variables
open Variables

infix 4 _∶_≼_

data _∶_≼_ (Γ : Ctx n) : Rel (Struct n) 0ℓ where
  ≼-refl   : Γ ∶ α ≈ β → Γ ∶ α ≼ β
  ≼-∅      : UnrCx Γ α → Γ ∶ [] ≼ α
  ≼-wk     : Γ ∶ (α₁ ∥ α₂) ; (β₁ ∥ β₂) ≼ (α₁ ; β₁) ∥ (α₂ ; β₂)
  ≼-trans  : Γ ∶ α ≼ β → Γ ∶ β ≼ γ → Γ ∶ α ≼ γ
  ≼-cong-; : Γ ∶ α ≼ α′ → Γ ∶ β ≼ β′ → Γ ∶ α ; β ≼ α′ ; β′
  ≼-cong-∥ : Γ ∶ α ≼ α′ → Γ ∶ β ≼ β′ → Γ ∶ α ∥ β ≼ α′ ∥ β′

≼-isPreorder : (Γ : Ctx n) → Bin.IsPreorder (Γ ∶_≈_) (Γ ∶_≼_)
≼-isPreorder Γ = record
  { isEquivalence = ≈-isEquivalence Γ
  ; reflexive = ≼-refl
  ; trans = ≼-trans
  }

≼-preorder : Ctx n → Bin.Preorder _ _ _
≼-preorder Γ = record { isPreorder = ≼-isPreorder Γ }

module ≼-Reasoning {n} {Γ : Ctx n} = PreorderReasoning (≼-preorder Γ)

UnrCx≼-⇒-UnrCx : UnrCx Γ α → Γ ∶ α ≼ β → UnrCx Γ β
UnrCx≼-⇒-UnrCx Uα (≼-refl eq) = allCx-≈ eq Uα
UnrCx≼-⇒-UnrCx Uα (≼-∅ Uβ) = Uβ
UnrCx≼-⇒-UnrCx ((Uα₁ ∥ Uα₂) ; (Uβ₁ ∥ Uβ₂)) ≼-wk = (Uα₁ ; Uβ₁) ∥ (Uα₂ ; Uβ₂)
UnrCx≼-⇒-UnrCx Uα (≼-trans α≼γ γ≼β) = UnrCx≼-⇒-UnrCx (UnrCx≼-⇒-UnrCx Uα α≼γ) γ≼β
UnrCx≼-⇒-UnrCx (U₁ ; U₂) (≼-cong-; α≼β₁ α≼β₂) = UnrCx≼-⇒-UnrCx U₁ α≼β₁ ; UnrCx≼-⇒-UnrCx U₂ α≼β₂
UnrCx≼-⇒-UnrCx (U₁ ∥ U₂) (≼-cong-∥ α≼β₁ α≼β₂) = UnrCx≼-⇒-UnrCx U₁ α≼β₁ ∥ UnrCx≼-⇒-UnrCx U₂ α≼β₂
