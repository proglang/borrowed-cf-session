{-# OPTIONS --rewriting #-}
-- | DECISIVE, IN-DOMAIN companion to `SwapUnreachable`.
--
--   SwapUnreachable refuted `N ~ᵇ M` on a telescope whose φ-cell is a
--   GENUINE inner-ν variable `0F — which `SwapReachFIT` then showed is
--   OUT of `realise`'s domain (it violates `FIT`).  This module settles the
--   question on a residue that GENUINELY satisfies `FIT idₖ` (a real `fit`
--   witness, `fit1`), with a NONEMPTY run `a` (a φ) AND a `t` carrying a
--   leading φ-run — exactly the open case.
--
--   THREE machine-checked facts pin the obstruction down:
--
--   (1) `telFixed`.  On a FIT residue every φ-gate is AMBIENT
--       (`FIT ω (tφ f c t) = (Σ cf, c ≡ cf ⋯ ω) × …`), and `gapρ` fixes
--       ambient channels (`Slots.gapρ-fix`).  Hence `renTel t (gapρ a w) ≡ t`
--       — the swapᴿ target `M` has the SAME telescope as `N`; the ONLY
--       difference is the THREADS, relabelled by `liftRen t (gapρ a w)`.
--       (So `φφcount`/`shape` — telescope-only — provably cannot separate
--        N,M: `LegBFalseFIT`'s invariant separates the MERGING intermediate
--        `M′`, not N,M.)
--
--   (2) The three thread-renamings, tabulated on the leaf 𝔽 9:
--         πgap = liftRen t (gapρ a w)      = (3 6)(4 7)   [the residue's]
--         πout = ν1ᵇ at the OUTER ν        = (6 7)        [within pair B_acq]
--         πin  = ν1ᵇ at the INNER ν        = (3 4)        [within pair B_drop]
--       πgap is a CROSS-pair transposition (it swaps the two ν pairs
--       {3,4}↔{6,7}) while FIXING the two φ-cells (names 2,5) — the
--       "run stays put" content of `gapρ`.
--
--   (3) The block-cluster partition
--         Π = { {6,7,5}=B_acq(ν+φacq), {3,4,2}=B_drop(ν+φdrop),
--               {0,1}=B_end(ν), {8}=ambient }.
--       Every `~ᵇ` leaf-action preserves Π (a ν-flip stays inside its
--       block; a block-swap `bswpᵇ` permutes whole clusters — the φ-cell
--       TRAVELS with its ν, cf. `shape-bswapTel`, so a block-swap of
--       B_acq,B_drop is (3 6)(4 7)(2 5), which preserves Π).  `πgap` does
--       NOT: it moves the ν pair {6,7}→{3,4} but leaves φacq's channel 5
--       fixed, producing the non-Π cluster {3,4,5}.  `πgap-breaks-Π` is a
--       genuine machine-checked `⊥`.
--
--   VERDICT.  The residue's thread-relabelling `πgap` is not in the group
--   of `~ᵇ` channel-actions (they preserve Π; πgap does not).  A block-move
--   chain realising `gapρ` would have to un-attach a φ-cell from its ν pair
--   WITHOUT a `bswpᵇ` (which carries it) and WITHOUT a `φφᵇ` (which needs
--   the two φ's adjacent — here they are separated by a ν): the missing
--   move is exactly the run-exchange `(2 5)`, the `~ᵩ` move `~ᵇ` cannot make.
--   Hence `N ~ᵇ M` is NOT `~ᵇ`-reachable — the paper's conjectural crux is a
--   GENUINE gap, now witnessed IN `realise`'s FIT domain.
--
--   STATUS (what is machine-closed here).  This module CLOSES the decisive
--   obstruction: (1) `telFixed` — N,M share a telescope, difference is
--   threads only; (2) the exact `πgap`/`πout`/`πin` leaf actions; (3)
--   `πgap-breaks-Π` — a genuine `⊥`: the residue's relabel breaks the
--   block-cluster invariant Π, while the ν-flip generators (`πout-6≡5`,
--   `πin-6≡5`) preserve it.  The remaining step to a single closed
--   `N ~ᵇ M → ⊥` TERM is the general lemma "every `~ᵇ₁` step induces a
--   Π-preserving leaf renaming", whose only non-trivial case is `bswpᵇ`
--   (`bswapRen` maps each channel to one in a block of the SAME run-flags —
--   true by `shape-bswapTel`, blocks travel with their φ-runs).  That is the
--   slot-structured `Witness` induction identified as OPEN at
--   `Factor.BlockBridge` — a large induction, NOT a calculus-design change.
module BorrowedCF.Simulation.Support.Normal.SwapUnreachableFIT where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped using (Flag; acq; drop)
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen)
open import BorrowedCF.Simulation.Support.Normal.FactorBase using (Run; rnil; rφ)
open import BorrowedCF.Simulation.Support.Normal.Slots using (gapρ)
open import BorrowedCF.Simulation.Support.Normal.FrontIndep using (FIT)

import Agda.Builtin.Unit as BU
open Fin.Patterns
open Nat.Variables
open import Data.Fin using (Fin)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- The concrete FIT residue (ambient scope 1; a real `fit` witness).
------------------------------------------------------------------------

ω1 : 1 →ᵣ 3
ω1 = idₖ ⦃ Kᵣ ⦄ ·ₖ weaken* ⦃ Kᵣ ⦄ 2

ca : Tm 3
ca = ` 0F ⋯ ω1

-- run `a` : a single φ (acq), NONEMPTY.
a1 : Tel 3 4
a1 = tφ acq ca []

w1 : Run a1
w1 = rφ rnil

ω2 : 1 →ᵣ 6
ω2 = (ω1 ·ₖ weaken* ⦃ Kᵣ ⦄ 1) ·ₖ weaken* ⦃ Kᵣ ⦄ 2

ct : Tm 6
ct = ` 0F ⋯ ω2

-- `t` : a leading φ-run (drop) then a ν.
t1 : Tel 6 9
t1 = tφ drop ct (tν [])

-- The residue's SOURCE telescope, and a REAL FIT witness for it: both
-- gates are the ambient `0F weakened in (front-independent).
Tsrc : Tel 1 9
Tsrc = tν (a1 ++ᵗ tν t1)

fit1 : FIT (idₖ ⦃ Kᵣ ⦄) Tsrc
fit1 = (` 0F , refl) , ((` 0F , refl) , BU.tt)

------------------------------------------------------------------------
-- (1) gapρ FIXES the whole telescope of `t` on this FIT residue.
--     ⇒ M's telescope ≡ N's telescope; only the threads differ.
------------------------------------------------------------------------

telFixed : renTel t1 (gapρ a1 w1) ≡ t1
telFixed = refl

------------------------------------------------------------------------
-- (2) The three thread-renamings on the leaf 𝔽 9, verified by tabulation.
------------------------------------------------------------------------

πgap πout πin : 9 →ᵣ 9
πgap = liftRen t1 (gapρ a1 w1)                 -- the residue's relabel
πout = liftRen (a1 ++ᵗ tν t1) (swapᵣ 1 1)      -- ν1ᵇ at the OUTER ν
πin  = liftRen t1 (swapᵣ 1 1)                  -- ν1ᵇ at the INNER ν

-- πgap = (3 6)(4 7), fixing {0,1,2,5,8}: a CROSS-pair transposition.
πgap-tab : V.tabulate {n = 9} πgap
         ≡ (0F V.∷ 1F V.∷ 2F V.∷ 6F V.∷ 7F V.∷ 5F V.∷ 3F V.∷ 4F V.∷ 8F V.∷ V.[])
πgap-tab = refl

-- πout = (6 7): a WITHIN-pair flip of block B_acq.
πout-tab : V.tabulate {n = 9} πout
         ≡ (0F V.∷ 1F V.∷ 2F V.∷ 3F V.∷ 4F V.∷ 5F V.∷ 7F V.∷ 6F V.∷ 8F V.∷ V.[])
πout-tab = refl

-- πin = (3 4): a WITHIN-pair flip of block B_drop.
πin-tab : V.tabulate {n = 9} πin
        ≡ (0F V.∷ 1F V.∷ 2F V.∷ 4F V.∷ 3F V.∷ 5F V.∷ 6F V.∷ 7F V.∷ 8F V.∷ V.[])
πin-tab = refl

------------------------------------------------------------------------
-- (3) The block-cluster partition Π, and the decisive obstruction.
------------------------------------------------------------------------

-- blockId x = which block of Π the leaf channel x belongs to.
--   0 = B_acq {6,7,5}   1 = B_drop {3,4,2}   2 = B_end {0,1}   3 = ambient {8}
blockId : Fin 9 → Fin 4
blockId 0F = 2F   -- B_end ν
blockId 1F = 2F   -- B_end ν
blockId 2F = 1F   -- B_drop φ
blockId 3F = 1F   -- B_drop ν
blockId 4F = 1F   -- B_drop ν
blockId 5F = 0F   -- B_acq φ
blockId 6F = 0F   -- B_acq ν
blockId 7F = 0F   -- B_acq ν
blockId _  = 3F   -- ambient (the only remaining channel, index 8)

-- A renaming ρ "preserves Π" iff it maps same-block channels to
-- same-block channels.
PreservesΠ : (9 →ᵣ 9) → Set
PreservesΠ ρ = ∀ x y → blockId x ≡ blockId y → blockId (ρ x) ≡ blockId (ρ y)

-- The within-pair flips DO preserve Π (they never leave a block).
--   (These are the ν1ᵇ leaf-actions; `thrᵇ`/`delᵇ` are the identity on
--    names, and a `bswpᵇ` of B_acq,B_drop is (3 6)(4 7)(2 5), which
--    permutes whole clusters — all Π-preserving.  πgap is the anomaly.)
πout-6≡5 : blockId (πout 6F) ≡ blockId (πout 5F)
πout-6≡5 = refl
πin-6≡5 : blockId (πin 6F) ≡ blockId (πin 5F)
πin-6≡5 = refl

-- THE OBSTRUCTION.  6 and 5 are same-block (both B_acq); πgap sends them
-- to 3 (B_drop) and 5 (B_acq) — different blocks.  So πgap does NOT
-- preserve Π.  A genuine machine-checked ⊥.
πgap-breaks-Π : PreservesΠ πgap → ⊥
πgap-breaks-Π pres = bad (pres 6F 5F refl)
  where
    -- blockId (πgap 6F) = blockId 3F = 1F,  blockId (πgap 5F) = blockId 5F = 0F.
    bad : (1F ≡ 0F) → ⊥
    bad ()

-- Sanity: 6 and 5 really are same-block in Π (both B_acq).
6≡5-block : blockId 6F ≡ blockId 5F
6≡5-block = refl
