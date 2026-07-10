-- | Reduct-side translation for the reverse RU-Drop reflection.  After R-Drop
--   the head bind block goes 1 → 0, so U[reduct] heads with φ acq (ϕ[0]=acq).
--   νσᵈ⁰ is νσᵈ with the head Ub block removed (head width 0); drop-bodyeq0 is
--   the head-0 analog of Drop.drop-bodyeq (φ acq instead of φ drop).
module BorrowedCF.Simulation.Backward.DropGoB where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP
import BorrowedCF.Processes.Untyped as UP
open import BorrowedCF.Processes.Translation using (Ub[_])
open import Data.Nat.ListAction using (sum)
open Fin.Patterns

νσᵈ⁰ : ∀ {m n} (c b₂ : ℕ) (σ : m →ₛ n)
     → (sum (0 ∷ c ∷ []) + sum (b₂ ∷ []) + m) →ₛ (3 + n)
νσᵈ⁰ c b₂ σ =
  ((λ i → Ub[ c + 0 ] (` 0F , 1F , *) i ⋯ weaken* ⦃ Kᵣ ⦄ 0)
    ++ₛ Ub[ b₂ + 0 ] (* , 2F , *))
  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 0)

drop-bodyeq0 : ∀ {m n} (c b₂ : ℕ) (σ : m →ₛ n)
               (P₀ : TP.Proc (sum (0 ∷ c ∷ []) + sum (b₂ ∷ []) + m))
             → U[ TP.ν (0 ∷ c ∷ []) (b₂ ∷ []) P₀ ] σ
               ≡ UP.ν (UP.φ UP.acq (U[ P₀ ] (νσᵈ⁰ c b₂ σ)))
drop-bodyeq0 c b₂ σ P₀ = refl
