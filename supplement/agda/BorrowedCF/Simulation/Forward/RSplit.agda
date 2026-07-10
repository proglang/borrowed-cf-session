-- | Forward simulation, R-RSplit.  Single untyped step: the ported ⊎-returning
--   proof `U-rsplit-step` (Simulation.Theorems.Splits) already builds
--   `RU-Struct front (Bφ-lift C₁ (Bφ-lift B leaf-fire)) back` — one `UR.─→ₚ`
--   (RU-RSplit allocates the fresh φ-drop) under the φ-nest transposes.  Here it
--   is restated with the clean single-step codomain and delegated to.
module BorrowedCF.Simulation.Forward.RSplit where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Support.Theorems.Splits using (U-rsplit-step)
open import BorrowedCF.Terms using (module SplitRenamings)

U-rsplit→ : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m} {B₁ B₂ B : TP.BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  → {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  → {P : TP.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  → (let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
     Γ ; g ⊢ₚ TP.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
                  (TP.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ TP.∥ P))
  → (let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
     U[ TP.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
             (TP.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ TP.∥ P) ] σ
       UR.─→ₚ
     U[ TP.ν (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B
             (TP.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))) ⊗ (` 𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F)) ]* ⟫ TP.∥ (P TP.⋯ₚ 𝐒.rwk)) ] σ)
U-rsplit→ σ Vσ cc {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P =
  U-rsplit-step σ Vσ cc {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
