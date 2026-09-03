-- Backward simulation `UntypedSoup → Typed`: the example suite of
-- `Simulation/BackwardSoup/PLAN.md` §3.
--
-- Every one of the eleven soup rules gets a positive example: a closed
-- `P : Typed.Proc 0`, the literal configuration `flatten P`, a concrete
-- soup step out of it, a typed step `P ─→ₚ P′`, and either
-- `flatten P′ ≡ C′` by `refl` or, where that fails, the weaker relation
-- that does hold plus the failure mode it illustrates.
--
--   rule          naive proposition           what holds instead
--   ------------  --------------------------  --------------------------
--   RUS-Exp       holds (`refl`)              --                (F5 ok)
--   RUS-Fork      holds (`refl`)              --
--   RUS-New       holds at the canonical      `GlobalImage P′ C′`, the
--                 channel index; fails at     permutation absorbed by
--                 any other index             `logicalChannels`     (F2)
--   RUS-LSplit    holds (`refl`)              --
--   RUS-RSplit    holds at the canonical      nothing: the reduct is no
--                 slot `k`; fails at every    flattening at all; the two
--                 other admissible `k`        differ by a slot swap (F3)
--   RUS-Drop      fails: no typed rule        nothing: `Pf4` is well
--                 applies to the redex        typed and its reduct is
--                                             no flattening         (F4)
--   RUS-Discard   fails likewise              likewise, via `Pf4b`  (F4)
--   RUS-Acquire   holds -- `⊢ᴮ` makes the     --
--                 typed rule complete here
--   RUS-Close     fails (channel counts       `GlobalImage P′ C′` with
--                 differ)                     the dead channel as
--                                             garbage                (F1)
--   RUS-Com       holds (`refl`), also with   --
--                 the partners swapped
--   RUS-Choice    holds (`refl`), also with   --
--                 the partners swapped
--
-- The `RUS-Drop` / `RUS-Discard` rows are the substance of this suite.  `Pf4`
-- and `Pf4b` of `Probes.agda` are WELL TYPED (`f4-typing`, `f4b-typing`); the
-- soup fires on a handle that is not the head of the first binder group, where
-- `R-Drop` / `R-Discard` cannot; and the soup reduct is the flattening of no
-- well-typed process (`f4-reduct-shape-untypable`).  No formulation of the
-- backward statement absorbs that -- PLAN.md §5 lists the possible remedies.
--
-- Recommended generalised statement (see the report accompanying this
-- suite):  for a well-typed closed `P` and a soup step
-- `C ─→ₚ C′` out of `C = flatten P`, there is `P′` with `P ─→ₚ P′` and
-- `GlobalImage P′ C′` UP TO a per-endpoint renumbering of phi slots --
-- but only after `RUS-RSplit` has been restricted so that it can fire only
-- where the typed rule can: the new boundary must go to the position
-- determined by the split handle's group.
module BorrowedCF.Simulation.BackwardSoup.Examples where

open import BorrowedCF.Simulation.BackwardSoup.Examples.Base public
open import BorrowedCF.Simulation.BackwardSoup.Examples.Exp
open import BorrowedCF.Simulation.BackwardSoup.Examples.Growth
open import BorrowedCF.Simulation.BackwardSoup.Examples.Splits
open import BorrowedCF.Simulation.BackwardSoup.Examples.Handles
open import BorrowedCF.Simulation.BackwardSoup.Examples.Sync
open import BorrowedCF.Simulation.BackwardSoup.Examples.Probes
