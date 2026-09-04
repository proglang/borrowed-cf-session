-- | Lifting reflected reductions through located process contexts.
module BorrowedCF.Simulation.BackwardSoup.Lift where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Reduction.Processes.Typed as TypedReduction

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug)

------------------------------------------------------------------------
-- A typed reduction reconstructed at a located leaf remains a reduction of
-- the enclosing process.  The calculus only reduces the left parallel
-- component, so a right-context step is exposed and restored with
-- commutativity.

plug-red :
  ∀ {k n} →
  (ctx : ProcessContext k n) →
  {P P′ : Typed.Proc k} →
  P TypedReduction.─→ₚ P′ →
  plug ctx P TypedReduction.─→ₚ plug ctx P′
plug-red hole red = red
plug-red (par-left ctx Q) red =
  TypedReduction.R-Par (plug-red ctx red)
plug-red (par-right Q ctx) red =
  TypedReduction.R-Struct Typed.∥-comm
    (TypedReduction.R-Par (plug-red ctx red)) Typed.∥-comm
plug-red (bind B₁ B₂ ctx) red =
  TypedReduction.R-Bind (plug-red ctx red)
