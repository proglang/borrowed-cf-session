-- HandleCount analogue for R-Acq: the consumed handle is 0F (position 0) of the
-- front bind group  zero ∷ suc b₁ ∷ B₁ , the simplest case of the split
-- bookkeeping, adapted to the current `structBinder` / TP-Res context shape.

module BorrowedCF.Simulation.Support.AcqHandle where

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Struct; _∥_; cast)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Typed using (BindGroup; structBinder)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.Support.StructDom
  using (count-structBinder-lt; count-weaken*-lo; count-⋯ᵣwkʳ-↑ˡ)

open import Data.Fin.Base using (_↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ)

open Nat.Variables
open Fin.Patterns
open Nat using (_<_; _≤_; s≤s; z≤n)
open import Data.List using (_∷_)

-- The bind-context produced by inv-ν of the acq redex counts the handle 0F
-- exactly once.  The context is the TP-Res shape with outer binder
-- B₁ := C₁ = zero ∷ suc b₁ ∷ B₁ and outer binder B₂ := B₂.
count-handle-acq : ∀ (b₁ : ℕ) (B₁ B₂ : BindGroup) {m} (γ : Struct m) →
  let C₁ = zero ∷ suc b₁ ∷ B₁ in
  count 0F
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder B₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum B₂)) ) ≡ 1
count-handle-acq b₁ B₁ B₂ {m} γ = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    C₁ : BindGroup
    C₁ = zero ∷ suc b₁ ∷ B₁
    0<C₁ : 0 < sum C₁
    0<C₁ = s≤s z≤n
    -- 0F : 𝔽 (sum C₁ + sum B₂ + m) is (0F ↑ˡ sum B₂) ↑ˡ m definitionally (zero ↑ˡ k = zero).
    partA : count 0F (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum B₂)) (0F ↑ˡ sum B₂)
          ■ count-⋯ᵣwkʳ-↑ˡ (sum B₂) (structBinder C₁) 0F
          ■ count-structBinder-lt C₁ 0F 0<C₁
    partB : count 0F (structBinder B₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder B₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) (0F ↑ˡ sum B₂)
          ■ cong (count (0F ↑ˡ sum B₂)) (wkˡ≡weaken* (sum C₁) (structBinder B₂))
          ■ count-weaken*-lo (sum C₁) (structBinder B₂) (0F ↑ˡ sum B₂) 0↑<C₁
      where
        0↑<C₁ : Fin.toℕ (Fin.zero {b₁ + sum B₁} ↑ˡ sum B₂) < sum C₁
        0↑<C₁ = subst (_< sum C₁) (sym (toℕ-↑ˡ (Fin.zero {b₁ + sum B₁}) (sum B₂))) 0<C₁
        wkˡ≡weaken* : ∀ b {k} (δ : Struct k) → δ 𝐂S.⋯ᵣ 𝐂S.wkˡ b ≡ δ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ b
        wkˡ≡weaken* b δ = 𝐂S.⋯-cong δ (λ x → sym (𝐂S.weaken*~wkˡ ⦃ 𝐂S.Kᵣ ⦄ b x))
    partC : count 0F (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum B₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum B₂) γ (Fin.zero {b₁ + sum B₁ + sum B₂ + m}) (s≤s z≤n)

-- The scope of the acq redex factors as 0 + suc rest.
acqN-eq : ∀ (b₁ : ℕ) (B₁ B₂ : BindGroup) {m} →
  0 + suc ((b₁ + sum B₁) + sum B₂ + m) ≡ sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m
acqN-eq b₁ B₁ B₂ = refl

-- The thinning's missing point (cast of zero ↑ʳ zero) is the handle 0F.
mp≡handle-acq : ∀ (b₁ : ℕ) (B₁ B₂ : BindGroup) {m} →
  Fin.cast (acqN-eq b₁ B₁ B₂ {m}) (0 ↑ʳ 0F) ≡ 0F
mp≡handle-acq b₁ B₁ B₂ = refl
