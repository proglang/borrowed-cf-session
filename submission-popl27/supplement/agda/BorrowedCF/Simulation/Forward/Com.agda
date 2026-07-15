-- | Forward simulation, R-Com.  Single untyped step: the send/recv rendezvous
--   fires once (RU-Com under RU-Res∘Bφ-lift), with the φ-nest transposes
--   absorbed into RU-Struct.  The core proof lives in Theorems.Com.U-com-step;
--   here we restate it as the clean single-step forward lemma.
module BorrowedCF.Simulation.Forward.Com where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Reduction.Processes.Untyped as UR
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Simulation.Support.Theorems.Com using (U-com-step)

U-com : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {γ : Struct m} {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
  → {E₁ E₂ : Frame* (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → {P : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → {e : Tm (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → (V : Value e)
  → (let wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
     Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
       ((T.⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
         T.∥ T.⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
         T.∥ (P T.⋯ₚ wkρ)))
  → (let wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
     U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
                T.∥ T.⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
                T.∥ (P T.⋯ₚ wkρ)) ] σ
       UR.─→ₚ
      U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂)
              ((T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P) ] σ)
U-com = U-com-step
