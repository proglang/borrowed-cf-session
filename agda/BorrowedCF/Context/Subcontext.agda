{-# OPTIONS --rewriting #-}

module BorrowedCF.Context.Subcontext where

import Relation.Binary.Reasoning.Preorder as PreorderReasoning

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base
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

;-≼-∥ : Γ ∶ α ; β ≼ α ∥ β
;-≼-∥ {α = α} {β} =
  let open ≼-Reasoning in
  begin α        ; β         ≈⟨ ;-cong ∥-unit₂ ∥-unit₁ ⟨
        (α ∥ []) ; ([] ∥ β)  ≲⟨ ≼-wk ⟩
        (α ; []) ∥ ([] ; β)  ≈⟨ ∥-cong ;-unit₂ ;-unit₁ ⟩
        α        ∥ β         ∎


≼-≗ : Γ₁ ≗ Γ₂ → Γ₁ ∶ α ≼ β → Γ₂ ∶ α ≼ β
≼-≗ eq (≼-refl x) = ≼-refl (≈-≗ eq x)
≼-≗ eq (≼-∅ x) = ≼-∅ (allCx-≗ eq x)
≼-≗ eq ≼-wk = ≼-wk
≼-≗ eq (≼-trans x x₁) = ≼-trans (≼-≗ eq x) (≼-≗ eq x₁)
≼-≗ eq (≼-cong-; x x₁) = ≼-cong-; (≼-≗ eq x) (≼-≗ eq x₁)
≼-≗ eq (≼-cong-∥ x x₁) = ≼-cong-∥ (≼-≗ eq x) (≼-≗ eq x₁)

module _ where
  open Un using (_⊆_)

  allCx-strengthen : ∀ {ℓ} {P : Pred 𝕋 ℓ} → Γ ∶ α ≼ β → AllCx P Γ β → AllCx P Γ α
  allCx-strengthen (≼-refl eq)    C         = allCx-≈ (≈-sym eq) C
  allCx-strengthen (≼-∅ x)        C         = []
  allCx-strengthen (≼-trans  x y) C         = allCx-strengthen x (allCx-strengthen y C)
  allCx-strengthen (≼-cong-; x y) (C₁ ; C₂) = allCx-strengthen x C₁ ; allCx-strengthen y C₂
  allCx-strengthen (≼-cong-∥ x y) (C₁ ∥ C₂) = allCx-strengthen x C₁ ∥ allCx-strengthen y C₂
  allCx-strengthen ≼-wk ((C₁ ; C₂) ∥ (C₁′ ; C₂′)) = (C₁ ∥ C₁′) ; (C₂ ∥ C₂′)

  allCx-weaken : ∀ {ℓ} {P : Pred 𝕋 ℓ} → (Unr ⊆ P) → Γ ∶ α ≼ β → AllCx P Γ α → AllCx P Γ β
  allCx-weaken f (≼-refl eq) C = allCx-≈ eq C
  allCx-weaken f (≼-∅ U)     C = allCx-map f U
  allCx-weaken f ≼-wk ((C₁ ∥ C₂) ; (C₁′ ∥ C₂′)) = (C₁ ; C₁′) ∥ (C₂ ; C₂′)
  allCx-weaken f (≼-trans x y) C = allCx-weaken f y (allCx-weaken f x C)
  allCx-weaken f (≼-cong-; x y) (C₁ ; C₂) = allCx-weaken f x C₁ ; allCx-weaken f y C₂
  allCx-weaken f (≼-cong-∥ x y) (C₁ ∥ C₂) = allCx-weaken f x C₁ ∥ allCx-weaken f y C₂

  unrCx-weaken : Γ ∶ α ≼ β → UnrCx Γ α → UnrCx Γ β
  unrCx-weaken = allCx-weaken id

  ≼-map⁺ : {f : 𝕋 → 𝕋} → (Unr ⊆ Unr ∘ f) → Γ ∶ α ≼ β → f ∘ Γ ∶ α ≼ β
  ≼-map⁺ Uf (≼-refl x) = ≼-refl (≈-map⁺ Uf x)
  ≼-map⁺ Uf (≼-∅ x) = ≼-∅ (allCx-gmap Uf x)
  ≼-map⁺ Uf ≼-wk = ≼-wk
  ≼-map⁺ Uf (≼-trans x x₁) = ≼-trans (≼-map⁺ Uf x) (≼-map⁺ Uf x₁)
  ≼-map⁺ Uf (≼-cong-; x x₁) = ≼-cong-; (≼-map⁺ Uf x) (≼-map⁺ Uf x₁)
  ≼-map⁺ Uf (≼-cong-∥ x x₁) = ≼-cong-∥ (≼-map⁺ Uf x) (≼-map⁺ Uf x₁)

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
