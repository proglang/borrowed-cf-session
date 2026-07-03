module BorrowedCF.Simulation.BC2Probe where

open import Data.Vec.Functional as F using ()
open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed

open Fin.Patterns

-- A width-2 block for session (msg ‼ ⟨⊤⟩ ; end ⁇):
--   intra-block position 0 = ⟨ msg ‼ ⟨⊤⟩ ⟩  (a USED, non-end New borrow)
--   intra-block position 1 = ⟨ end ⁇ ⟩       (the close endpoint)
-- The `end` sits at position 1F, so no typed R-Close (fires at inj 0F) closes
-- it; the preceding `msg` borrow is not a skip (R-Discard cannot clear it).
-- Yet the UNTYPED RU-Close fires on the substituted `end` redex.
g2 : Ctx 2
g2 = ⟨ msg ‼ `⊤ ⟩ F.∷ (⟨ end ⁇ ⟩ F.∷ (λ ()))

bc2 : BindCtx′ (msg ‼ `⊤ ; end ⁇) 2 g2
bc2 = cons (λ { (() ; _) }) ≃-refl (λ _ → refl)
        (cons (λ ()) ≃-skipʳ (λ _ → refl) (nil skip))
