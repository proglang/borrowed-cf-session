-- | Pointwise substitution collapse for the reverse RU-Drop reflection.
--   After R-Drop fires, the head bind block width drops 1 → 0, so the reduct's
--   translation substitution is νσᵈ⁰ (head width 0).  The redex substitution is
--   νσᵈ 0 c b₂ σ (head width 1).  Skipping the consumed head channel 0F with the
--   weaken-by-1 renaming (Fin.suc) lands exactly in the c-block / b₂-block /
--   σ-region — which is νσᵈ⁰.  The head Ub[1] block occupies only index 0F, and
--   the c-block e₂ slots (` 0F , 1F , wk *) vs (` 0F , 1F , *) coincide because
--   wk * = * ⋯ weakenᵣ = * (units are weaken-invariant); every branch is refl.
module BorrowedCF.Simulation2.Backward.DropCollapse where

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Simulation2.Backward.Drop    using (νσᵈ)
open import BorrowedCF.Simulation2.Backward.DropGoB using (νσᵈ⁰)

drop-collapse : ∀ {m n} (c b₂ : ℕ) (σ : m →ₛ n)
                (i : 𝔽 (sum (0 ∷ c ∷ []) + sum (b₂ ∷ []) + m))
              → νσᵈ⁰ c b₂ σ i ≡ νσᵈ 0 c b₂ σ (Fin.suc i)
drop-collapse c b₂ σ i with Fin.splitAt (c + 0 + (b₂ + 0)) i
... | inj₂ u = refl
... | inj₁ d with Fin.splitAt (c + 0) d
...   | inj₂ w = refl
...   | inj₁ v = refl
