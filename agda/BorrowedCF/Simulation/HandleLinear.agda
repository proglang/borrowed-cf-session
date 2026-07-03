-- The fact the new `lsplit : ¬ Skips s → …` premise gives us: a lsplit'd
-- channel ⟨ s ; s′ ⟩ is never unrestricted.  This is what discharges the
-- `¬ Unr (handle)` hypothesis of `≼⇒count≤` in the confinement proof.

module BorrowedCF.Simulation.HandleLinear where

open import BorrowedCF.Prelude
open import BorrowedCF.Types

-- Unr ⟨ s ; s′ ⟩ = Skips (s ; s′), which forces Skips s — contradicting ¬ Skips s.
¬Skips⇒¬Unr-seq : ¬ Skips s → ¬ (Unr ⟨ s ; s′ ⟩)
¬Skips⇒¬Unr-seq _ ⟨ () ⟩
