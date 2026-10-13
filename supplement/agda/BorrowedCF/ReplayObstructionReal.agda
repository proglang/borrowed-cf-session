-- | THE RECURRING OBSTRUCTION, in the ACTUAL calculus (no abstraction).
--
--   Same content as ReplayObstruction, but with the real untyped reduction
--   `RU-LSplit` and the real structural-congruence generator `ν-swap′`, on a
--   concrete process.  Everything here typechecks against the project's own
--   `Processes.Untyped` / `Reduction.Processes.Untyped`.
module BorrowedCF.ReplayObstructionReal where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types using (skip)
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)
open import BorrowedCF.Reduction.Processes.Untyped

open Fin.Patterns

------------------------------------------------------------------------
-- A concrete process.  Under one ν (which binds the dual pair 0F , 1F), a
-- thread is poised to `lsplit` the innermost bound channel 0F, next to an
-- inert unit thread.  `𝓒[ e₁ × x × e₂ ] = (e₁ ⊗ ` x) ⊗ e₂` is the handle
-- triple; the middle component `x` is the channel the op acts on.
------------------------------------------------------------------------

body : Proc 2
body = ⟪ K (`lsplit skip) ·¹ 𝓒[ * × 0F × * ] ⟫ ∥ ⟪ * ⟫

Rp : Proc 0
Rp = ν body

------------------------------------------------------------------------
-- (1) R takes a REAL step by the actual rule `RU-LSplit`, firing on channel
--     0F (with the empty telescope Φ = []φ and the empty frame).
------------------------------------------------------------------------

step : Rp ─→ₚ
  ν ( ⟪ 𝓒[ * × 0F × * ] ⊗ 𝓒[ * × 0F × * ] ⟫ ∥ ⟪ * ⟫ )
step = RU-LSplit []φ []

------------------------------------------------------------------------
-- (2) R is ν-swap-congruent (the ACTUAL generator `ν-swap′`) to S, whose body
--     is `body ⋯ₚ swapᵣ 1 1` — the renaming that exchanges the two ν-bound
--     channels 0F ↔ 1F.
------------------------------------------------------------------------

Sp : Proc 0
Sp = ν ( body ⋯ₚ swapᵣ 1 1 )

swapped : Rp ≋′ Sp
swapped = ν-swap′

-- The swap moved the op off 0F onto 1F: S's redex names 1F.
S-reads-1F : Sp ≡ ν ( ⟪ K (`lsplit skip) ·¹ 𝓒[ * × 1F × * ] ⟫ ∥ ⟪ * ⟫ )
S-reads-1F = refl

------------------------------------------------------------------------
-- (3) THE FAILURE.  `RU-LSplit` (empty frame) fires only on a redex whose
--     channel is 0F.  S's redex is on 1F, so the step cannot be replayed:
--     S is not the source of any such rule instance (matching would force
--     the channels 1F ≡ 0F).
------------------------------------------------------------------------

stuck : ∀ {e₁ e₂ P} →
        Sp ≢ ν ( ⟪ K (`lsplit skip) ·¹ 𝓒[ e₁ × 0F × e₂ ] ⟫ ∥ P )
stuck ()
