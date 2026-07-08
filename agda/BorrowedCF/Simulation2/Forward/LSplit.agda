-- | Forward simulation, R-LSplit.  Single untyped step: the ported ⊎-returning
--   proof `U-lsplit-step` (Simulation.Theorems.Splits, via SplitsH2) already
--   builds `RU-Struct front (Bφ-lift C₁ (Bφ-lift B leaf-fire)) back` — one
--   `UR.─→ₚ` under the φ-nest transposes.  Here it is restated with the clean
--   single-step codomain and delegated to.
module BorrowedCF.Simulation2.Forward.LSplit where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Theorems.Splits using (U-lsplit-step)
open import BorrowedCF.Terms using (module SplitRenamings)

U-lsplit→ : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m} {B₁ B₂ B : TP.BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
  → {E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  → {P : TP.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)}
  → (let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
     Γ ; g ⊢ₚ TP.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
                  (TP.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ TP.∥ P))
  → (let module 𝐒 = SplitRenamings B₁ B₂ (sum B) in
     U[ TP.ν (B₁ ++ (q + suc b₁) ∷ B₂) B
             (TP.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ TP.∥ P) ] σ
       UR.─→ₚ
     U[ TP.ν (B₁ ++ (q + suc (suc b₁)) ∷ B₂) B
             (TP.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫ TP.∥ (P TP.⋯ₚ 𝐒.lwk)) ] σ)
U-lsplit→ σ Vσ cc {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P =
  U-lsplit-step σ Vσ cc {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
