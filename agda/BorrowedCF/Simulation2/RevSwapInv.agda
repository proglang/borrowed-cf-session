module BorrowedCF.Simulation2.RevSwapInv where

-- Self-contained swap involution on typed processes, needed by RevSkipNorm's
-- block-2 normalization (the ν-swap sandwich reconciles a there-and-back block
-- swap, which cancels to the identity by swapₚ-inv).  Copied verbatim from
-- BorrowedCF.TypedEq so RevSkipNorm does not depend on that (heavier) module.

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Typed

open Nat.Variables

⋯ₚ-id≗ : (P : Proc n) {ϕ : n →ᵣ n} → ϕ ≗ id → P ⋯ₚ ϕ ≡ P
⋯ₚ-id≗ ⟪ e ⟫ eq = cong ⟪_⟫ (⋯-id e eq)
⋯ₚ-id≗ (P ∥ Q) eq = cong₂ _∥_ (⋯ₚ-id≗ P eq) (⋯ₚ-id≗ Q eq)
⋯ₚ-id≗ (ν B₁ B₂ P) eq = cong (ν B₁ B₂) (⋯ₚ-id≗ P (id↑* _ eq))

swap-swap : ∀ a b {n} (x : 𝔽 (a + b + n)) → swapᵣ b a (swapᵣ a b x) ≡ x
swap-swap a b {n} x =
  cong (Fin.join (a + b) n ∘ Sum.map₁ (Fin.swap b))
       (Fin.splitAt-join (b + a) n (Sum.map₁ (Fin.swap a) (splitAt (a + b) x)))
  ■ cong (Fin.join (a + b) n) (mm (splitAt (a + b) x))
  ■ Fin.join-splitAt (a + b) n x
  where
    mm : (s : 𝔽 (a + b) ⊎ 𝔽 n) → Sum.map₁ (Fin.swap b) (Sum.map₁ (Fin.swap a) s) ≡ s
    mm (inj₁ z) = cong inj₁ (Fin.swap-involutive a z)
    mm (inj₂ w) = refl

swapₚ-inv : ∀ {a b n} (P : Proc (a + b + n)) → (P ⋯ₚ swapᵣ a b) ⋯ₚ swapᵣ b a ≡ P
swapₚ-inv {a} {b} P = fusionₚ P (swapᵣ a b) (swapᵣ b a) ■ ⋯ₚ-id≗ P (swap-swap a b)
