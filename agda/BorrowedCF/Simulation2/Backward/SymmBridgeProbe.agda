-- | MACHINE-TEST of the STAR-CODOMAIN coarsening for the reverse simulation
--   `U-symm` strict bridge, per the parent research task.  See report.
module BorrowedCF.Simulation2.Backward.SymmBridgeProbe where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevUCong using (U-not-φ; U-≋-escapes; Pesc)
  renaming (σ₀ to σ₀ᴿ)
open import BorrowedCF.Simulation2.Backward.NonEpsRoadblock
  using (B₁; B₂; P₀; σ₀; image; Simg; P̃; peeled)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; suc; _+_)
open import Relation.Nullary using (¬_)

open Fin.Patterns

------------------------------------------------------------------------
-- (A)  ν-swap′  admits a STRICT propositional image bridge.
--
--   The untyped ν-swap′ image  Simg  is DEFINITIONALLY  U[ P̃ ] σ₀,  the
--   translation of the TYPED ν-swap target  P̃ = ν B₂ B₁ (P₀ ⋯ swapᵣ …).
--   NonEpsRoadblock only refuted a CHAIN-LENGTH-0 recognition (len (≋-chain) ≥ 1);
--   the STRICT ≡ the Star / strict-image route actually needs is REAL and holds
--   by refl.  So ν-swap′ is NOT an obstruction to strict-image reflection.
------------------------------------------------------------------------

strict-swap-test : Simg ≡ U[ P̃ ] σ₀
strict-swap-test = refl

-- …and the source is TYPED-≋ to the recogniser (one typed ν-swap′ link), so the
-- bridge is a genuine typed-structural-congruence bridge, image→image.
typed-swap : TP.ν B₁ B₂ P₀ TP.≋ P̃
typed-swap = Eq*.return TP.ν-swap′

------------------------------------------------------------------------
-- (B)  νφ-comm′  does NOT — and the STAR codomain is provably powerless.
--
--   The νφ-comm′ escape  R = φ drop (ν …)  is φ-HEADED, and  U-not-φ  proves NO
--   image  U[ P′ ] σ  is ever φ-headed, for ANY typed P′.  Since this is
--   P′-UNIVERSAL, it holds for every P′ REACHABLE by a typed reduction sequence
--   Pesc ─→ₚ* P′ — the Star premise is IGNORED (`_`).  So allowing a whole
--   reduction SEQUENCE (the parent's KEY NEW ANGLE) gives NO leverage: R is not a
--   strict image of any ─→ₚ*-reachable P′.  Decisive, and DISTINCT from
--   NonEpsRoadblock (chain-length recognition of ν-swap′): here the wall is the
--   φ-head structural invariant on νφ-comm′.
------------------------------------------------------------------------

no-star-strict-νφ :
  ∀ (P′ : TP.Proc 0) → Star TR._─→ₚ_ Pesc P′ → proj₁ U-≋-escapes ≢ U[ P′ ] σ₀ᴿ
no-star-strict-νφ P′ _ = proj₂ (proj₂ U-≋-escapes) P′
