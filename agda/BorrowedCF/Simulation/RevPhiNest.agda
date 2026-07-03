module BorrowedCF.Simulation.RevPhiNest where

-- | φ-telescope-aware transport engine for the reverse simulation.
--
--   sim← (Reverse.agda) takes its input up to the weak equivalence  R ≈ U[ P ] σ
--   (≈ = EqClosure (≋ ∪ ─→ᵃ), RevAdmin).  Its ε case IS a strict image and feeds
--   sim←ᵍ directly; the non-ε case must handle a genuine ≈-prefix.
--
--   This module supplies the STRUCTURAL-CONGRUENCE transport:
--
--     ≋*-sim : R ≋ S → R ─→ₚ Q → Σ Q′. (S ─→ₚ Q′) × (Q ≋ Q′)
--
--   obtained by folding the single-generator strong replay
--   RevCongStrong.≋′-sim-strong over the ≋-chain.  It is the "reduce up to ≋ on
--   the source, keep a ≋-related reduct" harmony that would let the reverse
--   simulation move a reduction from R to a ≋-equal S while retaining a *strict*
--   ≋ between the two reducts — which the tight  Q ─→ᶜ? Q′  codomain of sim← can
--   absorb (via one RU-Struct wrap).  It is HOLE-FREE and postulate-FREE.
--
--   MACHINE-CONFIRMED FINDING (2026-07).  Wiring ≋*-sim into sim←'s non-ε case
--     sim← (c ◅ cs) red = ⟨ Q₁,red₁,q≋ ← ≋*-sim (link c) red ;
--                           recurse sim← cs red₁ ; re-wrap via q≋ ⟩
--   TYPECHECKS but Agda REJECTS it with a TerminationIssue, pinpointing the call
--     sim←ᵍ … refl (≋*-sim (sym c₁ ◅◅ ≡→≋ eq) inner .proj₂.proj₁)
--   : sim←ᵍ's RU-Struct case bounces through sim← and re-enters sim←ᵍ with the
--   TRANSPORTED reduction, which is NOT structurally smaller than `inner`.  The
--   ∥-comm fallback of ≋*-sim wraps a left-reduction in a fresh RU-Struct (─→ₚ has
--   NO right-∥ rule, so ∥-comm cannot be genuinely replayed — RevCongStrong.
--   ∥-red-inv), hence ∣transported∣ can EXCEED ∣inner∣.  No well-founded measure on
--   reduction size survives, and the chain length is not preserved across the
--   bounce.  So the reduction-TRANSPORT route to closing sim← non-ε is genuinely
--   non-terminating — a fresh witness of the RevCongStrong obstruction, now shown
--   to hit sim← directly (not just ≋′-sim-strong in isolation).
--
--   A terminating closure must instead use the φ-DECOMPOSITION (NOT reduction
--   transport): recognise every image→image generator (∥-comm/assoc/unit, ν-ext/
--   swap/comm) via inv-U-∥ / inv-U-ν + U[_]'s ∥/ν homomorphism, keeping R and
--   `red` FIXED and varying only the ≋-related SOURCE P′ (so the ∥-comm loop never
--   arises), and handle the single image-escaping generator νφ-comm (U-not-φ rules
--   out φ-comm / φ-ext as image-adjacent) by pushing φ back inside ν with a
--   φ-head-count measure.  That νφ-comm sub-case needs `─→ₚ` renaming-stability
--   (red-⋯ₚ, absent) to replay the inner reduction under assocSwapᵣ 1 2, and the
--   image→image recognition needs `U-≋` (translation respects typed ≋), whose
--   ν-swap′/ν-comm′ cases reorder the φ-telescope under binder permutation (the
--   research-scale machinery of the forward Splits.agda).  This is therefore a
--   multi-module ≋-confluence/normalisation development, not a single-module fix;
--   RevUCong already machine-proves the STRICT reflection form is FALSE.

open import BorrowedCF.Prelude
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR

open import BorrowedCF.Simulation.RevCongStrong using (≋′±-sim-strong)

import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure)

open Nat.Variables

open UP using (Proc; _≋′_; _≋_)
open UR using (_─→ₚ_)

------------------------------------------------------------------------
-- Single-link transport (one SymClosure _≋′_ generator).
------------------------------------------------------------------------

≋±-sim : {R R′ Q : Proc n} → SymClosure _≋′_ R R′ → R ─→ₚ Q →
         Σ[ Q′ ∈ Proc n ] (R′ ─→ₚ Q′) × (Q ≋ Q′)
≋±-sim = ≋′±-sim-strong

------------------------------------------------------------------------
-- Full ≋-chain transport (fold over the equivalence closure).
--
--   Structural recursion on the ≋-chain; NON-mutual, so it always terminates
--   regardless of how the transported reduction grows.
------------------------------------------------------------------------

≋*-sim : {R S Q : Proc n} → R ≋ S → R ─→ₚ Q →
         Σ[ Q′ ∈ Proc n ] (S ─→ₚ Q′) × (Q ≋ Q′)
≋*-sim ε        red = _ , red , ε
≋*-sim (c ◅ cs) red
  with Q₁ , red₁ , q≋ ← ≋±-sim c red
  with Q′ , red′ , q≋′ ← ≋*-sim cs red₁ =
  Q′ , red′ , q≋ ◅◅ q≋′
