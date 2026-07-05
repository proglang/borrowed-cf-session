module BorrowedCF.Simulation.DropInteriorProbe where

-- MACHINE EVIDENCE for the (historical) reverse RU-Drop blocker, kept as the
-- record of WHY the drop fix landed the way it did.
--
-- A width-2 borrow block whose ret marker sits at INTERIOR position 1F is
-- BindCtx-constructible (bcd below; mirror of BC2Probe's close variant).  The
-- reverse RU-Drop reflects to a typed drop of exactly this ret marker, while
-- typed R-Drop fires only on a block-front handle — the two coincide only at
-- width 1.  With `drop PURE (∣ ℙ) the width-2 drop-ACTIVE state was well-typed
-- reachable (a sibling borrow ;-before the drop can hide in an evaluated
-- value), and no untyped-side fix exists: RU-Com must leave the surviving ret
-- triple byte-identical while the block shrinks 2→1, so ANY shrink-stable
-- translation makes width-1 and width-2-last ret triples indistinguishable —
-- a local RU-Drop discriminator is impossible.
--
-- RESOLUTION (this commit):
--  (1) `drop is now IMPURE (∣ 𝕀, Terms.agda): the LeftPat/frames-𝕀 squeeze
--      (RevComConfine) applies, so an ACTIVE drop admits no live borrow
--      ;-before it — the width-2 drop-active state is no longer typeable.
--      The BindCtx bcd below still exists (BindCtx is effect-blind); only the
--      active-redex configuration died.
--  (2) typed R-Drop is q-GENERALIZED to interior block-list position ∣B₁∣
--      (Reduction/Processes/Typed.agda, SplitRenamings.dwk) — the calculus
--      generalization this probe asked for; forward case: Theorems/DropQ.agda
--      (vacuity via dropVac-last/mid, firing via Bw-slide + leaf-dwk).
-- The reverse-direction width pin (width-2 refutation from the squeeze) lives
-- with the reverse drop case.

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
bcd = cons (λ { (() ; _) }) ≃-refl (λ _ → refl)
        (cons (λ ()) ≃-skipʳ (λ _ → refl) (nil skip))
