-- | MACHINE-CHECKED witness that the DEPTH / PROCESS-STRUCTURAL descent route
--   for the PhiTelescopeWF `Leaf` obligation (Backward.agda ?1/?2/?3) hits the
--   SAME φ-telescope wall as every prior reverse-simulation route — on a NEW
--   axis (nested-ν / φ depth) that NonEpsRoadblock's chain-length refutation did
--   not cover.
--
--   Setup.  In the φ-bearing simRes cases the ν-body image  X = φ fl X₀  is
--   φ-HEADED (Bisim.UB emits one φ per non-last bind-group element; U-not-φ).
--   `Leaf` must reflect a DIRECT non-Struct step  red : R ─→ₚ Y  with  R ≈ X,
--   where R is reached from X by the RU-Struct pre-links tel peeled — a ≋-chain
--   that may use ANY generator, including φ-comm′ and νφ-comm′.
--
--   The route case-splits `red` and tries to (a) DESCEND on the aligned
--   structural constructors (RU-Sync peels a φ, RU-Res peels a ν) and (b) reflect
--   the genuine channel ops via the proven ports.  BOTH halves are blocked:
--
--   (a) RU-Sync descent needs to identify which typed sync channel the head φ of
--       R corresponds to — i.e. φ-HEAD ALIGNMENT of ≈:
--         φ x R₀ ≈ φ fl X₀  ⟹  x ≡ fl   (and then R₀ ≈ X₀ to recurse).
--       `φ-align-⊥` REFUTES this: φ-comm′ swaps two φ cells and CHANGES the head
--       flag (acq ↔ drop), so ≈ carries no φ-head information.  The φ-peel that
--       the depth recursion needs cannot be set up.
--
--   (b) A genuine-op R (ν-headed: RU-Com/Close/Choice/LSplit/RSplit/Acquire, or
--       ∥-headed: RU-Close) is ≈-REACHABLE at the φ-headed X: `νφ-bridge` gives
--       ν (φ x P) ≈ φ x (ν …) from νφ-comm′, so an outer-ν redex sits one
--       νφ-comm′ link from the φ-headed body.  Reflecting it needs R itself to be
--       (≈) a strict image so a port can invert it — that is exactly
--       `Reverse-U-≋`, machine-REFUTED hole-free by `reverse-U-≋-⊥` (same νφ-comm′
--       escape, at the ν-body level here instead of the top level).
--
--   Conclusion: depth descent neither peels the φ (a) nor reflects the genuine op
--   (b) without the refuted φ-alignment / strict-image reflection.  It funnels
--   into the identical reverse-U-≋ wall as sim←-base — a genuine
--   calculus/statement design change, not tooling friction.
module BorrowedCF.Simulation2.Backward.DepthDescentWall where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Untyped as UP
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.RevUCong using (Reverse-U-≋; reverse-U-≋-⊥)

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _,_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

------------------------------------------------------------------------
-- (a)  φ-head alignment of ≈ is FALSE  ⇒  the RU-Sync φ-peel of the depth
--      recursion cannot even be set up.
------------------------------------------------------------------------

acq≢drop : UP.acq ≡ UP.drop → ⊥
acq≢drop ()

-- What descending a RU-Sync step  φ x R₀ ─→ φ x Y₀  against a φ-headed body
-- X = φ fl X₀  demands: the head flags must agree (so we know WHICH typed sync
-- channel is stepping) before we may recurse into the shorter telescope.
φ-align : Set
φ-align = ∀ {n} {x y : UP.Flag} {P Q : UP.Proc (suc n)}
        → UP.φ x P ≈ UP.φ y Q → x ≡ y

φ-align-⊥ : (P₀ : UP.Proc 2) → φ-align → ⊥
φ-align-⊥ P₀ align = acq≢drop (align e)
  where
    e : UP.φ UP.acq (UP.φ UP.drop P₀) ≈ _
    e = ≋⇒≈ (Eq*.return UP.φ-comm′)

------------------------------------------------------------------------
-- (b)  A ν-headed (genuine-op) redex is ≈-reachable at a φ-headed body via a
--      single νφ-comm′ link — the escape that reverse-U-≋-⊥ refutes.
------------------------------------------------------------------------

νφ-bridge : ∀ {n} {x : UP.Flag} {P : UP.Proc (3 + n)}
          → Σ[ Q ∈ UP.Proc (1 + n) ] (UP.ν (UP.φ x P) ≈ UP.φ x Q)
νφ-bridge = _ , ≋⇒≈ (Eq*.return UP.νφ-comm′)

-- The genuine-op leaf reflection is `Reverse-U-≋`, which is ⊥ for the typeable
-- escaping source Pesc = ν (1 ∷ 1 ∷ []) [] ⟪ drop · 0 ⟫ (whose ν-body image is
-- φ-headed).  Re-exported to name the exact wall the depth route funnels into.
genuine-op-leaf-wall = reverse-U-≋-⊥
