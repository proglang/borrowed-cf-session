module BorrowedCF.Simulation2.CongBisim where

-- | The untyped structural congruence ≋ is a STRONG BISIMULATION for the
--   untyped reduction ─→ₚ:
--
--       ≋-sim : R ≋ R′ → R ─→ₚ Q → Σ Q′. R′ ─→ₚ Q′ × Q ≋ Q′
--
--   This is the linchpin that unblocks the reverse simulation's ≋-prefix /
--   RU-Struct / φ-bearing cases (cf. BorrowedCF.Simulation2.Reverse, the
--   `reverse-U-≋` and `RU-Res φ-bearing` holes, which each ask for exactly the
--   "reduction-up-to-≋ on both sides" strengthening that ≋-sim provides).
--
--   The proof is short because the untyped reduction relation ─→ₚ *already
--   absorbs* the structural congruence on both sides, via its RU-Struct
--   constructor:
--
--       RU-Struct : P ≋ P′ → P′ ─→ₚ Q′ → Q′ ≋ Q → P ─→ₚ Q.
--
--   Given R ≋ R′ and R ─→ₚ Q, the witness Q′ = Q works: R′ ─→ₚ Q is closed by
--   RU-Struct (R′ ≋ R) (R ─→ₚ Q) (Q ≋ Q), where R′ ≋ R is symmetry of the
--   hypothesis and Q ≋ Q is reflexivity ε.  Hence ≋ is a strong bisimulation
--   (indeed the transported target Q′ can be taken *equal* to Q, so the
--   codomain leg Q ≋ Q′ is reflexive).

open import BorrowedCF.Prelude
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (ε)

open U using (_≋′_; _≋_)
open UR using (_─→ₚ_)

------------------------------------------------------------------------
-- ≋ absorbs into ─→ₚ from the left (the source leg).
------------------------------------------------------------------------

-- A ≋-prefix of a reducible process is itself reducible to the SAME reduct.
-- (This is RU-Struct read as "reduce up to ≋ on the source"; the reduct is
--  literally unchanged.)
≋-step : ∀ {n} {R R′ Q : U.Proc n} → R U.≋ R′ → R UR.─→ₚ Q → R′ UR.─→ₚ Q
≋-step c red = UR.RU-Struct (Eq*.symmetric _ c) red ε

------------------------------------------------------------------------
-- ≋ is a strong bisimulation for ─→ₚ.
------------------------------------------------------------------------

-- Single-step form (harmony against one ≋′ move).  We never need to case-split
-- on the ≋′ constructor: RU-Struct commutes ANY (chain of) congruence move(s)
-- past the reduction, keeping the reduct fixed.
≋′-sim : ∀ {n} {R R′ Q : U.Proc n} → R U.≋′ R′ → R UR.─→ₚ Q →
         Σ[ Q′ ∈ U.Proc n ] (R′ UR.─→ₚ Q′ × Q U.≋ Q′)
≋′-sim c red = _ , ≋-step (Eq*.return c) red , ε

-- Full form over the equivalence closure.
≋-sim : ∀ {n} {R R′ Q : U.Proc n} → R U.≋ R′ → R UR.─→ₚ Q →
        Σ[ Q′ ∈ U.Proc n ] (R′ UR.─→ₚ Q′ × Q U.≋ Q′)
≋-sim c red = _ , ≋-step c red , ε

-- Symmetric restatement (the bisimulation game from the other player): a step
-- on the ≋-related R′ is matched by a step from R to a ≋-equal reduct.  Since
-- ≋ is symmetric this is just ≋-sim applied to the flipped congruence.
≋-sim⁻ : ∀ {n} {R R′ Q′ : U.Proc n} → R U.≋ R′ → R′ UR.─→ₚ Q′ →
         Σ[ Q ∈ U.Proc n ] (R UR.─→ₚ Q × Q U.≋ Q′)
≋-sim⁻ c red = _ , ≋-step (Eq*.symmetric _ c) red , ε
