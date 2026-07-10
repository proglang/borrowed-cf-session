-- | Forward simulation, R-New.  Allocates the two channel triples; one untyped
--   step RU-New, wrapped by frame-plug* on the left and the ⊗-swap
--   reconciliation `rnew-bridge` on the right (the untyped RU-New pairs the
--   triples `0F⊗`1F while U[ R-New's rhs ] pairs them `1F⊗`0F; the swap is
--   absorbed by substituting the triples into the unswapped leaf tL).
--   Ported single-step; rnew-bridge inlined (its home ReverseInv is mid-migration).
module BorrowedCF.Simulation.Forward.New where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation.Support.FrameRename using (frame-fusion-gen; frame-cong)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋; Ub-V)

tL : ∀ {n} → Tm (4 + n)
tL = (((` 1F) ⊗ (` 2F)) ⊗ *) ⊗ (((` 0F) ⊗ (` 3F)) ⊗ *)

rnew-bridge : ∀ {m n} (E : Frame* m) (σ : m →ₛ n) (Vσ : VSub σ) →
  UP.ν (UP.φ UP.acq (UP.φ UP.acq UP.⟪
        (frame*-⋯ E σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]* ⟫))
    UP.≋
  U[ TP.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
        TP.⟪ (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 0F) ⊗ (` 1F) ]* ⟫ ] σ
rnew-bridge {m} {n} E σ Vσ =
  ≡→≋ (cong UP.ν (cong (UP.φ UP.acq) (cong (UP.φ UP.acq) (cong UP.⟪_⟫ bodyEq))))
  where
    A : 1 →ₛ (1 + (1 + (2 + n)))
    A = Ub[ 1 ] ((` 0F) , 1F , wk *) ·ₖ weaken* ⦃ Kᵣ ⦄ 1
    B : 1 →ₛ (1 + (1 + (2 + n)))
    B = Ub[ 1 ] ((` 0F) , suc (weaken* ⦃ Kᵣ ⦄ 1 1F) , wk *)
    Bσ : m →ₛ (1 + (1 + (2 + n)))
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 1
    σ′ : (1 + 1 + m) →ₛ (1 + (1 + (2 + n)))
    σ′ = (A ++ₛ B) ++ₛ Bσ
    VA : VSub A
    VA j = value-⋯ (Ub-V 1 (` 0F) 1F (wk *) V-` (value-⋯ V-K (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)) j)
                   (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)
    VB : VSub B
    VB j = Ub-V 1 (` 0F) (suc (weaken* ⦃ Kᵣ ⦄ 1 1F)) (wk *) V-`
                 (value-⋯ V-K (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)) j
    Vσ′ : VSub σ′
    Vσ′ = ++ₛ-VSub {σ₁ = A ++ₛ B}
            (++ₛ-VSub {σ₁ = A} VA VB)
            (weaken-VSub 1 (weaken-VSub 1 (weaken-VSub 2 Vσ)))
    weakenEq : Bσ ≗ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 4)
    weakenEq i = fusion (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ 1)
               ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1 ·ₖ weaken* ⦃ Kᵣ ⦄ 1)
    perF : (F : Frame m) → frame-⋯ (F ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame-⋯ F σ Vσ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 4
    perF F = frame-fusion-gen F (λ _ → V-`) Vσ′ (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x))
           ■ frame-cong F (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x)) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 4) (λ _ → V-`)) weakenEq
           ■ sym (frame-fusion-gen F Vσ (λ _ → V-`) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 4) (λ _ → V-`)))
    frameEqA : (E* : Frame* m) → frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4
    frameEqA []        = refl
    frameEqA (F ∷ E*) = cong₂ _∷_ (perF F) (frameEqA E*)
    bodyEq : (frame*-⋯ E σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]*
             ≡ ((E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 0F) ⊗ (` 1F) ]*) ⋯ σ′
    bodyEq = cong (_[ tL ]*) (sym (frameEqA E))
           ■ sym (frame-plug* (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′)

U-new : ∀ {m n} (σ : m →ₛ n) → VSub σ → {s : _} {E : Frame* m}
      → U[ TP.⟪ E [ K (`new s) ·¹ * ]* ⟫ ] σ
          UR.─→ₚ
        U[ TP.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
              TP.⟪ (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 0F) ⊗ (` 1F) ]* ⟫ ] σ
U-new σ Vσ {s} {E} =
  UR.RU-Struct
    (≡→≋ (cong UP.⟪_⟫ (frame-plug* E σ Vσ)))
    (UR.RU-New (frame*-⋯ E σ Vσ))
    (rnew-bridge E σ Vσ)
