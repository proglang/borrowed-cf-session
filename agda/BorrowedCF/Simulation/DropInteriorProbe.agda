module BorrowedCF.Simulation.DropInteriorProbe where

-- MACHINE EVIDENCE for the reverse RU-Drop blocker (simRes φ-bearing holes).
--
-- A width-2 borrow block whose ret marker sits at INTERIOR position 1F is
-- BindCtx-constructible (mirror of BC2Probe's close variant).  The reverse
-- RU-Drop reflects to a typed drop of exactly this ret marker, but typed
-- R-Drop fires only on the block-FRONT handle 0F of a width-1 head block —
-- and, unlike close/com/choice (impure, front-forced via the com-xS-min
-- squeeze on LeftPat frame stacks), `drop is PURE (∣ ℙ), so the impurity
-- front-forcing is unavailable: the earlier msg borrow may legitimately be
-- held inside an already-evaluated value (e.g. a pair) ;-before the active
-- drop redex.  Closing the reverse RU-Drop therefore needs the SAME calculus
-- generalization the splits received (R-Drop at interior block position q),
-- or a new typed rule — a typing/calculus design change.
--
-- (Compare: pieces after a ret marker force the residual ≃ skip, so the ret
-- is always the LAST borrow of its block; typed R-Drop's handle 0F therefore
-- only ever types at width 1.  The reverse handle is pinned by the image
-- geometry to the LAST index — the two only coincide at width 1.)

open import Data.Vec.Functional as F using ()
open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed

open Fin.Patterns

gd : Ctx 2
gd = ⟨ msg ‼ `⊤ ⟩ F.∷ (⟨ ret ⟩ F.∷ (λ ()))

-- the ret marker at interior position 1F, behind a live msg borrow.
bcd : BindCtx′ (msg ‼ `⊤ ; ret) 2 gd
bcd = cons (msg ‼ `⊤) ret (λ { (() ; _) }) ≃-refl (λ _ → refl)
        (cons ret skip (λ ()) ≃-skipʳ (λ _ → refl) (nil skip))
