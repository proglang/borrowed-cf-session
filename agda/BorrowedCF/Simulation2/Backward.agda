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
