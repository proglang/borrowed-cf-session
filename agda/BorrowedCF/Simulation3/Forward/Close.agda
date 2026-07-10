-- | Forward simulation, R-Close.  end‼/end⁇ rendezvous → two units, one
--   untyped step RU-Close, wrapped by the frame/telescope ≋ bridges.  Ported
--   single-step from the old Theorems R-Close case.
module BorrowedCF.Simulation3.Forward.Close where

open import BorrowedCF.Simulation3.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation3.Support.Frames using (frame-plug*; frame*-⋯; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation3.Support.FrameRename using (frame-fusion-gen; frame-cong)
open import BorrowedCF.Simulation3.Support.TranslationProperties using (≡→≋; Ub-V)

U-close : ∀ {m n} (σ : m →ₛ n) → VSub σ → {E₁ E₂ : Frame* m}
        → U[ TP.ν L.[ 1 ] L.[ 1 ]
              ( TP.⟪ E₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2 [ K (`end ‼) ·¹ (` 0F) ]* ⟫
              TP.∥ TP.⟪ E₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2 [ K (`end ⁇) ·¹ (` 1F) ]* ⟫ ) ] σ
            UR.─→ₚ
          U[ TP.⟪ E₁ [ * ]* ⟫ TP.∥ TP.⟪ E₂ [ * ]* ⟫ ] σ
U-close {m} {n} σ Vσ {E₁} {E₂} =
  UR.RU-Struct
    (≡→≋ (cong UP.ν (cong₂ UP._∥_
      (thr ‼ E₁ 0F t₁ (⋯-id t₁ {ϕ = weaken* ⦃ Kᵣ ⦄ 0} (λ _ → refl)))
      (thr ⁇ E₂ 1F t₂ refl))))
    (UR.RU-Close (frame*-⋯ E₁ σ Vσ) (frame*-⋯ E₂ σ Vσ))
    (≡→≋ (sym (cong₂ UP._∥_
      (cong UP.⟪_⟫ (frame-plug* E₁ σ Vσ))
      (cong UP.⟪_⟫ (frame-plug* E₂ σ Vσ)))))
  where
    t₁ : Tm (2 + n)
    t₁ = (K `unit ⊗ (` 0F)) ⊗ K `unit
    t₂ : Tm (2 + n)
    t₂ = (K `unit ⊗ (` 1F)) ⊗ K `unit
    σ₁ : 1 →ₛ (2 + n)
    σ₁ = Ub[ 1 + 0 ] (* , 0F , *)
    σ₂ : 1 →ₛ (2 + n)
    σ₂ = Ub[ 1 + 0 ] (* , 1F , *)
    Bσ : m →ₛ (2 + n)
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0
    σ′ : (1 + 1 + m) →ₛ (2 + n)
    σ′ = ((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0) ++ₛ σ₂) ++ₛ Bσ
    Vσ₁ : VSub σ₁
    Vσ₁ = λ j → Ub-V (1 + 0) * 0F * V-K V-K j
    Vσ₂ : VSub σ₂
    Vσ₂ = λ j → Ub-V (1 + 0) * 1F * V-K V-K j
    Vσ′ : VSub σ′
    Vσ′ = ++ₛ-VSub {σ₁ = (λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0) ++ₛ σ₂}
            (++ₛ-VSub {σ₁ = λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0} (weaken-VSub 0 Vσ₁) Vσ₂)
            (weaken-VSub 0 (weaken-VSub 0 (weaken-VSub 2 Vσ)))
    weakenEq : Bσ ≗ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2)
    weakenEq i = fusion (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 0) (weaken* ⦃ Kᵣ ⦄ 0)
               ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 0 ·ₖ weaken* ⦃ Kᵣ ⦄ 0)
    frameEqA : (E* : Frame* m) → frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2
    frameEqA []        = refl
    frameEqA (F ∷ E*) = cong₂ _∷_
      ( frame-fusion-gen F (λ _ → V-`) Vσ′ (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x))
      ■ frame-cong F (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x)) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`)) weakenEq
      ■ sym (frame-fusion-gen F Vσ (λ _ → V-`) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))) )
      (frameEqA E*)
    thr : (pol : Pol) (E* : Frame* m) (x : 𝔽 (1 + 1 + m)) (t : Tm (2 + n)) → σ′ x ≡ t →
          UP.⟪ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2 [ K (`end pol) ·⟨ 𝟙 ⟩ (` x) ]*) ⋯ σ′ ⟫
          ≡ UP.⟪ (frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end pol) ·⟨ 𝟙 ⟩ t ]* ⟫
    thr pol E* x t eq =
      cong UP.⟪_⟫ (frame-plug* (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′
                 ■ cong₂ _[_]* (frameEqA E*) (cong (K (`end pol) ·⟨ 𝟙 ⟩_) eq))
