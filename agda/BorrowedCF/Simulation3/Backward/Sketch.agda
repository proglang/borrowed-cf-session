-- | BACKWARD (completeness) simulation — PROOF SKETCH.
--
--   This module is DOCUMENTATION.  It states the backward-simulation goal against
--   the live definitions and records, in structured prose, exactly what is proved
--   and what remains open.  It imports only Simulation3.Base + base modules, so it
--   is self-contained (survives deletion of the old Simulation/ and Simulation2/
--   directories).  The partial backward proofs themselves lived in the deleted
--   Simulation2/Backward/* tree; their content is summarised here and preserved in
--   git history.
--
------------------------------------------------------------------------
-- THE GOAL
------------------------------------------------------------------------
--
--   Paper "Bisimulation" lemma (tex/.../sec/translation.tex:226), reverse half:
--   every untyped step of a translated process is matched by typed steps, up to
--   the administrative equivalence ≈.
--
--   The administrative equivalence (the user-approved "up-to-φ" relation) is
--       _≈_  =  EqClosure (UP._≋_  ∪  _─→ᵃ_)
--   with UP._≋_ untyped structural congruence and _─→ᵃ_ the discard-GC step.
--   Here the sketch states the goal with the untyped structural congruence ≋ in
--   the codomain (≈ ⊇ ≋); the full proof uses ≈, which additionally absorbs the
--   discard-GC administrative steps.
--
module BorrowedCF.Simulation3.Backward.Sketch where

open import BorrowedCF.Simulation3.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Context using (Ctx; Struct)
open TP using (_;_⊢ₚ_)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)

-- The backward-simulation statement (codomain shown with ≋; real proof: ≈ ⊇ ≋).
Backward-Sim-goal : Set
Backward-Sim-goal =
  ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
  → {Q : UP.Proc n} → U[ P ] σ UR.─→ₚ Q
  → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × (Q UP.≋ U[ P′ ] σ))

------------------------------------------------------------------------
-- STRATEGY
------------------------------------------------------------------------
--
--   sim← dispatches on the untyped step `red : U[P]σ ─→ₚ Q`, mirroring the
--   forward sim→.  All cases EXCEPT the structural-congruence rule
--       RU-Struct : R ≋ M → M ─→ₚ M′ → M′ ≋ Q → R ─→ₚ Q
--   reflect directly through the per-operation reflectors (dual to Forward.<Op>).
--   The whole difficulty of the reverse direction is the RU-Struct case: reflect a
--   step wrapped in a structural-congruence chain c₁ (before) and c₂ (after).
--
------------------------------------------------------------------------
-- SOLVED  (each was machine-checked, hole/postulate-free)
------------------------------------------------------------------------
--
--   • Leaf / thread / New / Fork / Discard / Par / Res              — direct duals.
--   • Channel ops Com / Close / Choice / LSplit / RSplit / Acquire / Drop
--     reflect on a STRICT image  R ≡ U[P]σ  via their reflector modules.
--   • RU-Struct, per-generator dispatch on the FIRST ≋′ link of c₁:
--       ∥-comm′/∥-assoc′/∥-unit′ : STRICT bridges — U[_] is a ∥-homomorphism, so
--         the reduct IS a strict image; recurse on the ∥-rearranged source and
--         prepend the typed ∥ move to the codomain Star.               [PROVEN]
--       ν-swap′, ν-comm′ : the untyped reduct  ν(body ⋯ swapᵣ)  is the strict
--         image with its ν-BOUND vars renamed; transport `inner` back onto the
--         strict image by reduction-equivariance  red-⋯ₚ (swapᵣ/assocSwapᵣ)  +
--         swap involutivity, reflect there, absorb the residual swap as a ≋ link
--         in the codomain.  This DISSOLVES the multi-block ν-swap "roadblock":
--         the equivariant route never invokes the flag-permuting φ-telescope
--         transposition (which is machine-false for multi-block groups).  [PROVEN]
--       νφ-comm′ / ν-ext′ / φ-ext′ (escapes) : route 3 — un-escape by the KNOWN
--         νφ-comm′ link, fire the ν-scoped step on the strict image, re-escape
--         absorbed into ≈.  drop-on-escape is vacuous (φ body is a ν, not a
--         thread); the single-link νφ-comm sync case is closed.          [PROVEN]
--       φ-comm′ : same-flag cells transport equivariantly.  Different-flag cells
--         are INESSENTIAL: on an image-order (acq-outermost) telescope a
--         different-flag φ-comm DISABLES the flag-sensitive redex, never exposes
--         one — machine-verified.  Since every U[P]σ is acq-outermost (first block
--         b₁ = 0 ⇒ ϕ[0]=acq is the OUTERMOST φ-cell), no different-flag φ-comm is
--         reflection-relevant.                                          [PROVEN]
--   • Termination: reduction-renaming preserves the measure ∣_∣, so the reflectors
--     drive a well-founded recursion with NO {-# TERMINATING #-}.        [PROVEN]
--
------------------------------------------------------------------------
-- OPEN  (the single residual)
------------------------------------------------------------------------
--
--   COMPOUND-CHAIN ESCAPE.  The per-generator reflectors compose over a c₁ whose
--   escape links (νφ-comm′/ν-ext′/φ-ext′) are FINAL (adjacent to the fired
--   direct step).  They do NOT yet compose when an escape is a NON-FINAL link of
--   a multi-generator c₁: the intermediate is a φ-headed / weakened-parallel
--   NON-image, and recognising a non-image as an image is machine-FALSE
--   (the deleted Simulation.RevUCong.reverse-U-≋-⊥, via "no image is φ-headed").
--   Equivalently: the existing engine abstracts the concrete chain c₁ into an
--   opaque ≈, at which point the specific escape link is no longer available to
--   un-escape, and the obligation bottoms at "reflect a direct step against a
--   merely ≈-related (not ≡) image".
--
--   This is NOT a calculus/counterexample obstruction: no reduction is exposed
--   only by an escape (RU-Res/RU-Sync already reach every under-binder redex).
--   Two closure routes, neither yet mechanised:
--     (i)  a CONCRETE-recursion restructure that pattern-matches c₁ link-by-link
--          throughout (never abstracting to ≈), so route 3 always fires; or
--     (ii) a targeted calculus change: restrict RU-Struct's congruence to the
--          head-PRESERVING generators, relegating the head-changing escapes
--          (νφ-comm′/ν-ext′/φ-ext′) to ≈ only — provided no redex needs scope
--          extrusion (a bounded, almost-certainly-true side condition).
--
------------------------------------------------------------------------
-- STATUS:  forward  = COMPLETE (Simulation3.Forward.sim→, 14/14).
--          backward = all per-generator reflectors + seed lemma + WF measure
--                     PROVEN; residual = compound-chain escape composition.
------------------------------------------------------------------------
