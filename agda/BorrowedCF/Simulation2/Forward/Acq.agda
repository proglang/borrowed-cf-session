-- | Forward simulation, R-Acq.  Single untyped step: the atomic RU-Acquire
--   fires once at the leaf (the width-0 first block always emits a `φ acq`
--   cell, ϕ[0] = acq), with the φ-nest transposes absorbed into RU-Struct.
--   The core proof lives in Theorems.Acq.U-acq-step; here we restate it as the
--   clean single-step forward lemma.
module BorrowedCF.Simulation2.Forward.Acq where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Reduction.Processes.Untyped as UR
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Simulation.Theorems.Acq using (U-acq-step)

U-acq→ : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m} {b₁ : ℕ} {B₁ B₂ : BindGroup}
  → {E : Frame* (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)}
  → {P : T.Proc (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)}
  → Γ ; g ⊢ₚ T.ν (zero ∷ suc b₁ ∷ B₁) B₂ (T.⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ T.∥ P)
  → U[ T.ν (zero ∷ suc b₁ ∷ B₁) B₂ (T.⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ T.∥ P) ] σ
       UR.─→ₚ
    U[ T.ν (suc b₁ ∷ B₁) B₂ (T.⟪ E [ ` zero ]* ⟫ T.∥ P) ] σ
U-acq→ = U-acq-step
