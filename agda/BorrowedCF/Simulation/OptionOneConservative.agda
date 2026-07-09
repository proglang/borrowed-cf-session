module BorrowedCF.Simulation.OptionOneConservative where

-- | THE CONSERVATIVITY PROOF for "Option 1" (endpoint-parameterising the
--   untyped channel-op rules so `_─→ₚ_` is closed under `ν-swap′`).
--
--   CLAIM.  Making `RU-LSplit` fire at EITHER ν-bound endpoint adds NOTHING to
--   the reduction relation: the would-be new `1F`-endpoint step is ALREADY
--   derivable in the CURRENT (0F-only) calculus, via `RU-Struct` + `ν-swap′`.
--
--   `lsplit-1F-adm` below proves exactly this, against the UNMODIFIED
--   `BorrowedCF.Reduction.Processes.Untyped` (the 0F-only `RU-LSplit`).  Hence
--   the parameterised reduction relation is EQUAL to the original — Option 1 is
--   a conservative REFORMULATION (it makes a `RU-Struct`-derived step primitive),
--   not a semantic change.  This is the machine-checked answer to "why is that
--   change okay": it doesn't change `_─→ₚ_` as a relation, only its presentation.
--
--   Read against BorrowedCF.Simulation.RevCongStrongLE, whose `ν-swap′ ∘
--   RU-LSplit` obstruction was about the *sc-preserving* (primitive) replay;
--   the plain step here IS derivable — just not sc-preservingly, which is the
--   whole reason Option 1 is wanted for the reverse engine yet harmless to the
--   reduction relation.

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Processes.Untyped
open import BorrowedCF.Simulation.Frames using (frame-plug₁)

import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Variables
open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

-- Frame* plugging commutes with renaming.
fp* : ∀ {m n} (E* : Frame* m) (ρ : m →ᵣ n) {t : Tm m} →
      (E* [ t ]*) ⋯ ρ ≡ (E* ⋯ᶠ* ρ) [ t ⋯ ρ ]*
fp* []       ρ = refl
fp* (E ∷ E*) ρ = frame-plug₁ E ρ (λ x → V-`) ■ cong ((E ⋯ᶠ ρ) [_]) (fp* E* ρ)

module _ {n : ℕ} (s : 𝕊 0) (F : Frame* (2 + n))
         {e₁ e₂ : Tm (2 + n)} {P : Proc (2 + n)} where

  -- The `1F`-endpoint lsplit redex and the reduct the parameterised rule WOULD
  -- produce (identical shape to `RU-LSplit`, but acting at endpoint 1F).
  body₁ reduct₁ : Proc (2 + n)
  body₁   = ⟪ F [ K (`lsplit s) ·¹ 𝓒[ e₁ × 1F × e₂ ] ]* ⟫ ∥ P
  reduct₁ = ⟪ F [ 𝓒[ e₁ × 1F × * ] ⊗ 𝓒[ * × 1F × e₂ ] ]* ⟫ ∥ P

  -- ν-swapping each lands on a genuine 0F-endpoint redex (swapᵣ 1 1 1F ≡ 0F,
  -- definitionally); the only non-refl step is the frame-plug distribution.
  lhsEq : ν (body₁ ⋯ₚ swapᵣ 1 1)
        ≡ ν ( ⟪ (F ⋯ᶠ* swapᵣ 1 1)
                 [ K (`lsplit s) ·¹ 𝓒[ e₁ ⋯ swapᵣ 1 1 × 0F × e₂ ⋯ swapᵣ 1 1 ] ]* ⟫
              ∥ (P ⋯ₚ swapᵣ 1 1) )
  lhsEq = cong (λ z → ν (⟪ z ⟫ ∥ (P ⋯ₚ swapᵣ 1 1)))
               (fp* F (swapᵣ 1 1) {t = K (`lsplit s) ·¹ 𝓒[ e₁ × 1F × e₂ ]})

  rhsEq : ν (reduct₁ ⋯ₚ swapᵣ 1 1)
        ≡ ν ( ⟪ (F ⋯ᶠ* swapᵣ 1 1)
                 [ 𝓒[ e₁ ⋯ swapᵣ 1 1 × 0F × * ] ⊗ 𝓒[ * × 0F × e₂ ⋯ swapᵣ 1 1 ] ]* ⟫
              ∥ (P ⋯ₚ swapᵣ 1 1) )
  rhsEq = cong (λ z → ν (⟪ z ⟫ ∥ (P ⋯ₚ swapᵣ 1 1)))
               (fp* F (swapᵣ 1 1) {t = 𝓒[ e₁ × 1F × * ] ⊗ 𝓒[ * × 1F × e₂ ]})

  -- The UNMODIFIED, 0F-only `RU-LSplit` fires on the ν-swapped body.
  core : ν (body₁ ⋯ₚ swapᵣ 1 1) ─→ₚ ν (reduct₁ ⋯ₚ swapᵣ 1 1)
  core = subst₂ _─→ₚ_ (sym lhsEq) (sym rhsEq)
           (RU-LSplit {s = s} {e₁ = e₁ ⋯ swapᵣ 1 1} {e₂ = e₂ ⋯ swapᵣ 1 1}
                      {P = P ⋯ₚ swapᵣ 1 1} (F ⋯ᶠ* swapᵣ 1 1))

  -- ADMISSIBILITY: the `1F`-endpoint lsplit step is derivable in the CURRENT
  -- calculus, via  ν-swap′  ∘  (0F-only) RU-LSplit  ∘  ν-swap′.
  lsplit-1F-adm : ν body₁ ─→ₚ ν reduct₁
  lsplit-1F-adm =
    RU-Struct (Eq*.return ν-swap′) core (Eq*.symmetric _ (Eq*.return ν-swap′))
