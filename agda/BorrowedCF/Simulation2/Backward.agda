-- | BACKWARD simulation — the CLEAN statement (current design, Route A).
--
--   Every untyped step of the translation is reflected by a typed step, UP TO
--   structural congruence ≋ on both sides.  The reflection is WEAK in exactly
--   one place: `discard, which the untyped runtime GCs on a spent ⟨skip⟩ handle
--   that the (ν-scoped) typed R-Discard cannot match on a bare thread — see
--   BorrowedCF.Simulation.DiscardProbe.  That silent GC is absorbed by ≈ =
--   EqClosure(≋ ∪ ─→ᵃ), whose ONLY administrative generator is now a-discard
--   (acquire's old `done`/cleanup GC is gone).  The old `─→ᶜ? trailing-cleanup
--   slack is therefore dropped; the typed side is ≤1 step (Star).
--
--   (A fully strong up-to-≋ statement — dropping ≈ for ≋ — is available only by
--    adding a thread-local typed discard rule; see the Q1 discussion.)
module BorrowedCF.Simulation2.Backward where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import BorrowedCF.Simulation.RevAdmin using (_≈_)

Backward-Sim : Set
Backward-Sim =
  ∀ {m} {n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
  → {R Q : UP.Proc n} → R ≈ U[ P ] σ → R UR.─→ₚ Q
  → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × Q ≈ U[ P′ ] σ)

-- ── sim← WIRING MAP (every untyped constructor MUST be dispatched; Agda's
--    coverage checker enforces completeness when sim← is assembled) ──
--   RU-Exp      → inv-U-⟪⟫ + ⋯→-reflect            leaf reflection
--   RU-Fork     → inv-U-⟪⟫ + frameApp-reflect      leaf reflection
--   RU-New      → frameApp-reflect + rnew inversion leaf reflection
--   RU-Discard  → silent (a-discard ⇒ ≈)           leaf (weak)
--   RU-LSplit   → lsplit-go   [RevLSplit]          channel-op reflection
--   RU-RSplit   → rsplit-go   [RevRSplit]          channel-op reflection
--   RU-Com      → com-go      [RevCom]             channel-op reflection
--   RU-Choice   → choice-go   [RevChoice]          channel-op reflection
--   RU-Close    → close-go    [RevClose]           channel-op reflection
--   RU-Acquire  → acq-go      [RevAcq]             channel-op reflection
--   RU-Par      → inv-U-∥ + recurse                inline (recursive)
--   RU-Sync     → vacuous at top level             inline
--   RU-Res      → simRes (φ-nest peel)             inline; ⊇ RU-Drop innermost  [HARD ×2]
--   RU-Struct   → non-ε ≈-chain engine             inline                       [HARD ×1]

open import BorrowedCF.Simulation2.Backward.Leaf using (bwd-exp; bwd-fork)
open import BorrowedCF.Simulation.RevAdmin using (≈-refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import Data.Product using (Σ-syntax; _×_)
open TP using (_;_⊢ₚ_)

-- sim← / sim←ᵍ (total dispatcher) is assembled once the channel-op reflections
-- and the 3 hard holes (simRes φ-nest ×2, non-ε engine) are ported/closed.
-- Wired leaf reflections live in BorrowedCF.Simulation2.Backward.Leaf.
