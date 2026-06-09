{-# OPTIONS --rewriting #-}

module BorrowedCF.Context.Subcontext where

import Relation.Binary.Reasoning.Preorder as PreorderReasoning

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Equivalence
open import BorrowedCF.Types

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

module _ {Γ : Ctx n} where
  open Bin.IsPreorder (≼-isPreorder Γ)
    using ()
    renaming
      ( ≲-respˡ-≈ to ≼-respˡ-≈
      ; ≲-respʳ-≈ to ≼-respʳ-≈
      )
    public

module ≼-Reasoning {n} {Γ : Ctx n} = PreorderReasoning (≼-preorder Γ)

≼-≗ : Γ₁ ≗ Γ₂ → Γ₁ ∶ α ≼ β → Γ₂ ∶ α ≼ β
≼-≗ eq (≼-refl x) = ≼-refl (≈-≗ eq x)
≼-≗ eq (≼-∅ x) = ≼-∅ (allCx-≗ eq x)
≼-≗ eq ≼-wk = ≼-wk
≼-≗ eq (≼-trans x x₁) = ≼-trans (≼-≗ eq x) (≼-≗ eq x₁)
≼-≗ eq (≼-cong-; x x₁) = ≼-cong-; (≼-≗ eq x) (≼-≗ eq x₁)
≼-≗ eq (≼-cong-∥ x x₁) = ≼-cong-∥ (≼-≗ eq x) (≼-≗ eq x₁)

module _ where
  open Un using (_⊆_)
  allCx-≼ : ∀ {ℓ} {P : Pred 𝕋 ℓ} → (Unr ⊆ P) → AllCx P Γ α → Γ ∶ α ≼ β → AllCx P Γ β
  allCx-≼ f C (≼-refl eq) = allCx-≈ eq C
  allCx-≼ f C (≼-∅ U) = allCx-map f U
  allCx-≼ f ((C₁ ∥ C₂) ; (C₁′ ∥ C₂′)) ≼-wk = (C₁ ; C₁′) ∥ (C₂ ; C₂′)
  allCx-≼ f C (≼-trans x y) = allCx-≼ f (allCx-≼ f C x) y
  allCx-≼ f (C₁ ; C₂) (≼-cong-; x y) = allCx-≼ f C₁ x ; allCx-≼ f C₂ y
  allCx-≼ f (C₁ ∥ C₂) (≼-cong-∥ x y) = allCx-≼ f C₁ x ∥ allCx-≼ f C₂ y

unrCx-≼ : UnrCx Γ α → Γ ∶ α ≼ β → UnrCx Γ β
unrCx-≼ = allCx-≼ id

module _ where
  open import Data.Fin.Subset
  open import Data.Fin.Subset.Properties
  open ≡-Reasoning

  ≼⇒dom⊆ : Γ ∶ α ≼ β → dom α ⊆ dom β
  ≼⇒dom⊆ (≼-refl x) = ⊆-reflexive (≈⇒dom≡ x)
  ≼⇒dom⊆ (≼-∅ x) = ⊥-elim ∘ ∉⊥
  ≼⇒dom⊆ (≼-wk {α₁} {α₂} {β₁} {β₂}) = ⊆-reflexive $
    dom ((α₁ ∥ α₂) ; (β₁ ∥ β₂)) ≡⟨⟩
    (dom α₁ ∪ dom α₂) ∪ (dom β₁ ∪ dom β₂)  ≡⟨ ∪-assoc (dom α₁ ∪ dom α₂) (dom β₁) (dom β₂) ⟨
    ((dom α₁ ∪ dom α₂) ∪ dom β₁) ∪ dom β₂  ≡⟨ cong (_∪ dom β₂) (∪-assoc (dom α₁) (dom α₂) (dom β₁)) ⟩
    (dom α₁ ∪ dom α₂ ∪ dom β₁) ∪ dom β₂    ≡⟨ cong (λ X → (dom α₁ ∪ X) ∪ dom β₂) (∪-comm (dom α₂) (dom β₁)) ⟩
    (dom α₁ ∪ dom β₁ ∪ dom α₂) ∪ dom β₂    ≡⟨ cong (_∪ dom β₂) (∪-assoc (dom α₁) (dom β₁) (dom α₂)) ⟨
    ((dom α₁ ∪ dom β₁) ∪ dom α₂) ∪ dom β₂  ≡⟨ ∪-assoc (dom α₁ ∪ dom β₁) (dom α₂) (dom β₂) ⟩
    (dom α₁ ∪ dom β₁) ∪ (dom α₂ ∪ dom β₂)  ≡⟨⟩
    dom ((α₁ ; β₁) ∥ (α₂ ; β₂)) ∎
  ≼⇒dom⊆ (≼-trans x y) = ⊆-trans (≼⇒dom⊆ x) (≼⇒dom⊆ y)
  ≼⇒dom⊆ (≼-cong-; x y) = x∈p∪q⁺ ∘ Sum.map (≼⇒dom⊆ x) (≼⇒dom⊆ y) ∘ x∈p∪q⁻ _ _
  ≼⇒dom⊆ (≼-cong-∥ x y) = x∈p∪q⁺ ∘ Sum.map (≼⇒dom⊆ x) (≼⇒dom⊆ y) ∘ x∈p∪q⁻ _ _

  dom⊈⇒⋠ : dom α ⊈ dom β → ¬ Γ ∶ α ≼ β
  dom⊈⇒⋠ dom⊈ α≼β = dom⊈ (≼⇒dom⊆ α≼β)

  `x⋠[] : ∀ {x} → ¬ Γ ∶ ` x ≼ []
  `x⋠[] {x = x} = dom⊈⇒⋠ λ ⁅x⁆⊆⁅⁆ → ∉⊥ (⁅x⁆⊆⁅⁆ (x∈⁅x⁆ x))

{-
_≼?_ : Bin.Decidable (Γ ∶_≼_)
(` x) ≼? (` y) = map′ (≼-refl ∘ ≈-reflexive ∘ cong `_) {!!} (x Fin.≟ y)
(` x) ≼? [] = no `x⋠[]
(` x) ≼? (α ∥ β) = {!!}
(` x) ≼? (α ; β) = {!!}
[] ≼? β = map′ ≼-∅ (unrCx-≼ []) (unrCx? β)
(α₁ ∥ α₂) ≼? β = {!!}
(α₁ ; α₂) ≼? β = {!!}
-}
