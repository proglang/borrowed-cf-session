-- | Lifting a reduction through a `ProcessContext` (agent G1, wave 2).
--
--   `Simulation/BackwardSoup/Locate.agda` presents a closed process as
--   `plug ctx Q`.  The typed reduction rules of
--   `Reduction/Processes/Typed.agda` have a congruence for the LEFT component
--   of a `∥` (`R-Par`) and for the body of a `ν` (`R-Bind`), but none for the
--   right component; `R-Struct` with `∥-comm` supplies it.  `red-in-ctx` is the
--   resulting congruence for a whole context, and `step-in-ctx` is its
--   composition with `R-Exp`.
module BorrowedCF.Safety.Progress.Redex.Context where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using () renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions using (_⋯→_)
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Processes.Typed
  using (_─→ₚ_; R-Exp; R-Par; R-Bind; R-Struct)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug)

open Nat.Variables

------------------------------------------------------------------------
-- A reduction of the hole is a reduction of the whole process.

red-in-ctx :
  {Q Q′ : Proc k} (ctx : ProcessContext k n) →
  Q ─→ₚ Q′ → plug ctx Q ─→ₚ plug ctx Q′
red-in-ctx hole red = red
red-in-ctx (par-left ctx R₀) red = R-Par (red-in-ctx ctx red)
red-in-ctx (par-right R₀ ctx) red =
  R-Struct ∥-comm (R-Par (red-in-ctx ctx red)) ∥-comm
red-in-ctx (bind B₁ B₂ ctx) red = R-Bind (red-in-ctx ctx red)

------------------------------------------------------------------------
-- An expression step at the hole thread is a process reduction.

step-in-ctx :
  {e e′ : Tm k} (ctx : ProcessContext k n) →
  e ⋯→ e′ → plug ctx ⟪ e ⟫ ─→ₚ plug ctx ⟪ e′ ⟫
step-in-ctx ctx step = red-in-ctx ctx (R-Exp step)
