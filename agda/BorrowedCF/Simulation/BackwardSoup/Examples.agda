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
--   RUS-Drop      counterexample ill-typed    --   the `Pf4` probe of
--                 under the strict rules      `Probes.agda` is no longer
--                                             well typed             (F4)
--   RUS-Discard   counterexample ill-typed    --   likewise for `Pf4b`  (F4)
--                 under the strict rules
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
-- The `RUS-Drop` / `RUS-Discard` counterexamples were removed by PLAN.md §5
-- remedy (i), i.e. by STRENGTHENING THE TYPE SYSTEM rather than the soup:
--   * `` `lsplit `` / `` `rsplit `` now require `¬ Skips s` of the FIRST
--     component too, so a split never produces a bare `⟨ skip ⟩` handle and
--     never moves a group's `acq` into a new group behind a `⟨ ret ⟩`;
--   * `BindCtx.cons-ret/acq` requires `¬ Skips s₂` (a boundary is formed only
--     in front of real work) and, like `BindCtx.cons-acq`, `AcqHeadCtx Γ₂`
--     (the first bound handle of a non-first group carries that group's
--     `acq`).
-- `Probes.agda` now carries checked refutations of exactly those premises for
-- `Pf4` and `Pf4b`.
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
