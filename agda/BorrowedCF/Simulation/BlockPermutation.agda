module BorrowedCF.Simulation.BlockPermutation where

-- | Permutation of φ^ binder blocks: φ-past-block and
--   φ^-swap : φ^ a (φ^ b X) ≋ φ^ b (φ^ a (X ⋯ₚ assocSwapᵣ b a)) — the
--   structural heart of the ν-swap reordering.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.BlockSwap
open import BorrowedCF.Simulation.Flatten

φ-past-block : ∀ b {m} (X : 𝐔.Proc (b + suc m)) →
               𝐔.φ (φ^ b X) 𝐔.≋ φ^ b (𝐔.φ (X 𝐔.⋯ₚ assocSwapᵣ b 1 {m}))
φ-past-block zero    X = ≡→≋ (cong 𝐔.φ (sym (⋯ₚ-id X assocSwap-01)))
φ-past-block (suc b) X =
     φ-past-block b (𝐔.φ X)
  ◅◅ φ^-cong b (Eq*.return 𝐔.φ-comm′
               ◅◅ ≡→≋ (cong 𝐔.φ (cong 𝐔.φ
                        (𝐔.fusionₚ X (assocSwapᵣ b 1 ↑) (assocSwapᵣ 1 1)
                         ■ 𝐔.⋯ₚ-cong X (R2 b)))))

φ^-swap : ∀ a b {m} (X : 𝐔.Proc (b + (a + m))) →
          φ^ a (φ^ b X) 𝐔.≋ φ^ b (φ^ a (X 𝐔.⋯ₚ assocSwapᵣ b a {m}))
φ^-swap zero    b X = φ^-cong b (≡→≋ (sym (⋯ₚ-id X (R-base-b0 b))))
φ^-swap (suc a) b X =
     φ^-cong a (φ-past-block b X)
  ◅◅ φ^-swap a b (𝐔.φ (X 𝐔.⋯ₚ assocSwapᵣ b 1))
  ◅◅ φ^-cong b (φ^-cong a (≡→≋ (cong 𝐔.φ
       (𝐔.fusionₚ X (assocSwapᵣ b 1) (assocSwapᵣ b a ↑)
        ■ 𝐔.⋯ₚ-cong X (R2' b a)))))
