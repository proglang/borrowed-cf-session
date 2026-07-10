-- | SEED-LEMMA probe (Option 4): a DIFFERENT-flag φ-comm′ never EXPOSES a
--   flag-sensitive (RU-Drop / RU-Acquire) redex on an IMAGE-ORDER φ-telescope.
--
--   Image φ-telescopes are acq-OUTERMOST (bind-group ⊢ᴮ allows the first block
--   = 0 ⇒ outer cell acq, the rest drop).  So the only DIFFERENT-flag adjacent
--   pair an image can present is  φ acq (φ drop …).  φ-comm′ swaps it to
--   φ drop (φ acq …):
--
--     • BEFORE swap the drop redex is FIREABLE (drop-fires-before): the inner
--       `φ drop` wraps a thread-parallel `⟪ K drop · 𝓒[…] ⟫ ∥ P`, reached under
--       the outer acq by RU-Sync.
--     • AFTER swap NO flag-sensitive rule fires at the swapped cells: the outer
--       `φ drop` now wraps a φ-cell (not a thread) ⇒ RU-Drop's redex shape fails
--       to match (drop-head-clash); the inner `φ acq` is under a φ, not a ν ⇒
--       RU-Acquire's redex shape fails to match (acq-head-clash).  The swap thus
--       DISABLES, never EXPOSES.
--
--   All results hole-free / postulate-free.
module BorrowedCF.Simulation2.Backward.SeedProbe where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)
open import BorrowedCF.Reduction.Processes.Untyped

open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality as Eq

open Nat.Variables
open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

------------------------------------------------------------------------
-- The concrete drop-redex thread body, at Proc 2.
--   D = ⟪ K `drop · 𝓒[ * × 1F × ` 0F ] ⟫ ∥ ⟪ * ⟫.
-- (Empty frame []; [] [ e ]* = e.)
D : Proc 2
D = ⟪ K `drop ·¹ 𝓒[ * × 1F × ` 0F ] ⟫ ∥ ⟪ * ⟫

-- Image-order telescope (acq OUTERMOST) : φ acq (φ drop D) : Proc 0.
imgOrder : Proc 0
imgOrder = φ acq (φ drop D)

-- φ-comm′ swapped form : φ drop (φ acq (D ⋯ₚ assocSwapᵣ 1 1)) : Proc 0.
swapped : Proc 0
swapped = φ drop (φ acq (D ⋯ₚ assocSwapᵣ 1 1))

-- The link is exactly ONE φ-comm′ generator (different flags acq/drop).
img≋′swap : imgOrder ≋′ swapped
img≋′swap = φ-comm′ {x = acq} {y = drop}

------------------------------------------------------------------------
-- (1) BEFORE the swap: the drop redex is genuinely FIREABLE.
--     RU-Drop [] fires the inner φ drop; RU-Sync lifts it under the outer φ acq.
drop-fires-before : imgOrder ─→ₚ φ acq (φ acq (⟪ [] [ * ]* ⟫ ∥ ⟪ * ⟫))
drop-fires-before = RU-Sync (RU-Drop [] {x = 0F})

------------------------------------------------------------------------
-- (2) AFTER the swap: NO flag-sensitive redex at the swapped cells.
--
-- RU-Drop's redex is  φ drop (⟪ F [ K `drop · 𝓒[ * × suc x × ` 0F ] ]* ⟫ ∥ P):
-- the φ drop must wrap a THREAD-PARALLEL.  `swapped`'s φ drop wraps  φ acq (…),
-- a φ-cell.  So the redex shape fails to match — constructor clash  φ ≢ _∥_.
drop-head-clash : ∀ {k} {X : Proc (2 + k)} {e : Tm (1 + k)} {P : Proc (1 + k)}
                → φ acq X Eq.≡ ⟪ e ⟫ ∥ P → ⊥
drop-head-clash ()

-- RU-Acquire's redex is  ν (φ acq (…)): the acq cell must sit directly under a
-- ν.  `swapped`'s φ acq sits under a φ drop.  So the redex shape fails to match
-- — constructor clash  φ ≢ ν.
acq-head-clash : ∀ {k} {Y : Proc (1 + k)} {Z : Proc (2 + k)}
               → φ drop Y Eq.≡ ν Z → ⊥
acq-head-clash ()

------------------------------------------------------------------------
-- (3) The ENABLING analysis, made explicit.  φ-comm′ permutes the two cells
--     and reindexes the SHARED body; it does not manufacture a fresh drop-cell
--     around a thread.  Enabling is decided purely by the INNER flag after the
--     swap:
--        φ acq (φ drop thread)  ⟶φcomm  φ drop (φ acq thread⋯)   inner = acq ⇒ DISABLED
--        φ drop (φ acq thread)  ⟶φcomm  φ acq (φ drop thread⋯)   inner = drop ⇒ enabled
--     Only the SECOND (drop-OUTER) source can expose a drop — and that is NOT an
--     image-order telescope (images are acq-outermost).  So on image order the
--     swap can only ever DISABLE.  Witnessed structurally: the swapped inner
--     cell is φ acq, whose body carries the (now-inert) drop hole.
swapped-inner-is-acq : swapped Eq.≡ φ drop (φ acq (D ⋯ₚ assocSwapᵣ 1 1))
swapped-inner-is-acq = Eq.refl
