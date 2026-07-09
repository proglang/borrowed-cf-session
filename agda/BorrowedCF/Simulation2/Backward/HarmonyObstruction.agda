-- | Machine witness: the push-through harmony invariant is UNSATISFIABLE for
--   the `∥-comm′ × RU-Par` case, because the untyped reduction relation has no
--   right-∥ (or general evaluation-context) congruence rule.
--
--   The harmony lemma the reverse non-ε engine needs is
--     ≋′-red : R ≋′ S → R ─→ Q → (Σ Q′. S ─→ Q′ × Q ≈ Q′) ⊎ (Q ≈ S)
--   with the INVARIANT (required for consumer termination — see the machine-
--   witnessed TerminationIssue in the earlier probe) that when `red` is a
--   PRIMITIVE, the produced `S ─→ Q′` is the SAME rule with the redex relocated,
--   NEVER an `RU-Struct` wrap.
--
--   Take the link `∥-comm′ : B ∥ ⟪ e₁ ⟫ ≋′ ⟪ e₁ ⟫ ∥ B` and the reduction
--   `RU-Par r : B ∥ ⟪ e₁ ⟫ ─→ B′ ∥ ⟪ e₁ ⟫`.  Relocating that step onto
--   `S = ⟪ e₁ ⟫ ∥ B` means reducing `B` — which now sits in the RIGHT operand.
--   The lemma below enumerates EVERY reduction of a process whose right operand
--   is an arbitrary `Rgt`: the only inhabitants are `RU-Par` (which fires the
--   LEFT operand) and `RU-Struct`.  There is no rule that fires the right
--   operand directly.  Hence the relocated `S ─→ Q′` can only be `RU-Struct`-
--   headed, violating the invariant — and `RU-Struct`-headed codomains are
--   exactly what the `sim←ᵍ` consumer loops on (proved separately).
--
--   Consequence: closing the reverse non-ε engine via harmony requires a
--   CALCULUS CHANGE — adding a right-∥ / general evaluation-context congruence
--   to `Reduction.Processes.Untyped._─→ₚ_` (or discharging the postulated
--   `⊢-≋` and reflecting ∥-rearrangements through `reverse-U-◈`, with the
--   φ-permutation links remaining genuine escapes per Simulation.RevUCong).
module BorrowedCF.Simulation2.Backward.HarmonyObstruction where

open import BorrowedCF.Prelude
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Every step of `Lft ∥ Rgt` fires the LEFT operand (RU-Par) or is RU-Struct.
-- No constructor fires the right operand `Rgt`: a primitive-headed relocation
-- of a right-branch redex does not exist.
∥-step-is-left-or-struct :
  ∀ {n} {Lft Rgt Q : UP.Proc n}
  → (Lft UP.∥ Rgt) UR.─→ₚ Q
  → (Σ[ Lft′ ∈ UP.Proc n ] ((Lft UR.─→ₚ Lft′) × (Q ≡ Lft′ UP.∥ Rgt)))
  ⊎ (Σ[ M ∈ UP.Proc n ] Σ[ M′ ∈ UP.Proc n ]
       ((Lft UP.∥ Rgt) UP.≋ M × (M UR.─→ₚ M′) × (M′ UP.≋ Q)))
∥-step-is-left-or-struct (UR.RU-Par r)         = inj₁ (_ , r , refl)
∥-step-is-left-or-struct (UR.RU-Struct c₁ r c₂) = inj₂ (_ , _ , c₁ , r , c₂)
