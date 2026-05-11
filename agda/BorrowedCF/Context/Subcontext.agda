{-# OPTIONS --rewriting #-}

module BorrowedCF.Context.Subcontext where

import Relation.Binary.Reasoning.Preorder as PreorderReasoning

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Types

open Nat.Variables
open Variables
open Un using (_⊆_)

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

allCx-≼ : ∀ {ℓ} {P : Pred 𝕋 ℓ} → (Unr ⊆ P) → AllCx P Γ α → Γ ∶ α ≼ β → AllCx P Γ β
allCx-≼ f C (≼-refl eq) = allCx-≈ eq C
allCx-≼ f C (≼-∅ U) = allCx-map f U
allCx-≼ f ((C₁ ∥ C₂) ; (C₁′ ∥ C₂′)) ≼-wk = (C₁ ; C₁′) ∥ (C₂ ; C₂′)
allCx-≼ f C (≼-trans x y) = allCx-≼ f (allCx-≼ f C x) y
allCx-≼ f (C₁ ; C₂) (≼-cong-; x y) = allCx-≼ f C₁ x ; allCx-≼ f C₂ y
allCx-≼ f (C₁ ∥ C₂) (≼-cong-∥ x y) = allCx-≼ f C₁ x ∥ allCx-≼ f C₂ y
