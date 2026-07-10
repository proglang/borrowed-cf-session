module BorrowedCF.Algorithmic.SplitLemmas where

open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (x∈⁅y⁆⇒x≡y; x∈p∪q⁻; ∉⊥)
import Data.Sum as Sum

open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)

open Nat.Variables

mob-y : {n : ℕ} {Γ : Ctx n} {y : 𝔽 n} → Unr (Γ y) → MobCx Γ (` y)
mob-y u = ` unr⇒mobile u

mob-COMMA-comm : {n : ℕ} {Γ : Ctx n} {α β : Struct n} → MobCx Γ α ⊎ MobCx Γ β → Γ ∶ α ; β ≈ β ; α
mob-COMMA-comm m = ≈-sym (∥/;-transmute m) ◅◅ ∥-comm ◅◅ ∥/;-transmute (Sum.swap m)

-- Merge a duplicate unrestricted variable (already present) into a context.
mutual
  mv : {n : ℕ} {Γ : Ctx n} (A : Struct n) {y : 𝔽 n} → y ∈ dom A → Unr (Γ y) → Γ ∶ A ∥ (` y) ≼ A
  mv (` z) {y} y∈ u with x∈⁅y⁆⇒x≡y z y∈
  ... | refl = ≼-refl (≈-sym (∥-dup (` u)))
  mv [] y∈ u = ⊥-elim (∉⊥ y∈)
  mv (α ∥ β) {y} y∈ u with x∈p∪q⁻ (dom α) (dom β) y∈
  ... | Sum.inj₁ y∈α =
    ≼-trans (≼-refl (∥-assoc ◅◅ ∥-cong ≈-refl ∥-comm ◅◅ ≈-sym ∥-assoc))
            (≼-cong-∥ (mv α y∈α u) (≼-refl ≈-refl))
  ... | Sum.inj₂ y∈β =
    ≼-trans (≼-refl ∥-assoc) (≼-cong-∥ (≼-refl ≈-refl) (mv β y∈β u))
  mv (α ; β) {y} y∈ u with x∈p∪q⁻ (dom α) (dom β) y∈
  ... | Sum.inj₁ y∈α =
    ≼-trans (≼-refl (∥/;-transmute (Sum.inj₂ (mob-y u)) ◅◅ ;-assoc
                     ◅◅ ;-cong ≈-refl (mob-COMMA-comm (Sum.inj₂ (mob-y u))) ◅◅ ≈-sym ;-assoc))
            (≼-cong-; (seq-mv α y∈α u) (≼-refl ≈-refl))
  ... | Sum.inj₂ y∈β =
    ≼-trans (≼-refl (∥/;-transmute (Sum.inj₂ (mob-y u)) ◅◅ ;-assoc))
            (≼-cong-; (≼-refl ≈-refl) (seq-mv β y∈β u))

  seq-mv : {n : ℕ} {Γ : Ctx n} (A : Struct n) {y : 𝔽 n} → y ∈ dom A → Unr (Γ y) → Γ ∶ A ; (` y) ≼ A
  seq-mv A y∈ u = ≼-trans (≼-refl (≈-sym (∥/;-transmute (Sum.inj₂ (mob-y u))))) (mv A y∈ u)

open import Data.Fin.Subset.Properties using (p⊆p∪q; q⊆p∪q; ⊆-trans; x∈⁅x⁆; x∈p∪q⁺)

∥-absorb : {n : ℕ} {Γ : Ctx n} {A : Struct n} (B : Struct n) →
           AllCx Unr Γ B → dom B ⊆ dom A → Γ ∶ A ∥ B ≼ A
∥-absorb [] _ _ = ≼-refl ∥-unit₂
∥-absorb {A = A} (` y) (` u) dom⊆ = mv A (dom⊆ (x∈⁅x⁆ y)) u
∥-absorb {A = A} (B₁ ∥ B₂) (U₁ ∥ U₂) dom⊆ =
  ≼-trans (≼-refl (≈-sym ∥-assoc))
    (≼-trans (≼-cong-∥ (∥-absorb B₁ U₁ (⊆-trans (p⊆p∪q (dom B₂)) dom⊆)) (≼-refl ≈-refl))
             (∥-absorb B₂ U₂ (⊆-trans (q⊆p∪q (dom B₁) (dom B₂)) dom⊆)))
∥-absorb {A = A} (B₁ ; B₂) (U₁ ; U₂) dom⊆ =
  ≼-trans (≼-refl (∥-cong ≈-refl (≈-sym (∥/;-transmute (Sum.inj₁ (UnrCx⇒MobCx U₁)))) ◅◅ ≈-sym ∥-assoc))
    (≼-trans (≼-cong-∥ (∥-absorb B₁ U₁ (⊆-trans (p⊆p∪q (dom B₂)) dom⊆)) (≼-refl ≈-refl))
             (∥-absorb B₂ U₂ (⊆-trans (q⊆p∪q (dom B₁) (dom B₂)) dom⊆)))

join-absorb : {n : ℕ} {Γ : Ctx n} (a : Dir) {A : Struct n} (B : Struct n) →
              AllCx Unr Γ B → dom B ⊆ dom A → Γ ∶ join a A B ≼ A
join-absorb 𝟙 B U dom⊆ = ∥-absorb B U dom⊆
join-absorb L {A} B U dom⊆ =
  ≼-trans (≼-refl (≈-sym (∥/;-transmute (Sum.inj₂ (UnrCx⇒MobCx U))))) (∥-absorb B U dom⊆)
join-absorb R {A} B U dom⊆ =
  ≼-trans (≼-refl (≈-sym (∥/;-transmute (Sum.inj₁ (UnrCx⇒MobCx U))) ◅◅ ∥-comm)) (∥-absorb B U dom⊆)
