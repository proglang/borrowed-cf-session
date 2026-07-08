-- | FORWARD simulation — the CLEAN statement.
--
--   Every typed process step is simulated by exactly ONE untyped step of the
--   translation.  This single-step form is available because acquire is now
--   ATOMIC (RU-Acquire consumes the sync cell and substitutes in one step — no
--   `done` flag, no RU-Cleanup), so no typed rule expands to two untyped steps,
--   and the φ-nest transposes are absorbed into RU-Struct (itself one ─→ₚ).
--
--   sim→ is assembled in this module by dispatch; each channel-op case is
--   proved in its own BorrowedCF.Simulation2.Forward.<Op> module.
module BorrowedCF.Simulation2.Forward where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)

Forward-Sim : Set
Forward-Sim =
  ∀ {m} {n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
  → {P′ : TP.Proc m} → P TR.─→ₚ P′
  → U[ P ] σ UR.─→ₚ U[ P′ ] σ
