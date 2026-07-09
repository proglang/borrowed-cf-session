-- | The reverse non-ε engine (Backward.agda ?0), structured by WELL-FOUNDED
--   recursion on the reduction measure ∣red∣ (RevCongStrong.∣_∣) — NOT Agda's
--   structural-termination checker, and with NO {-# TERMINATING #-} pragma.
--
--   This module machine-checks the TERMINATION half of the ?0 plan: the engine
--   dispatches on `red`, peels every leading RU-Struct node (∣inner∣ < ∣red∣ by
--   the ∣_∣ measure, since ∣ RU-Struct _ inner _ ∣ = suc ∣ inner ∣), and absorbs
--   BOTH congruence links c₁/c₂ into the codomain ≈ (≈-trans ∘ ≋⇒≈).  The
--   input-relation change (R ≈ U[P]σ  ↦  P″ ≈ U[P]σ, via ≈-sym/≈-trans across
--   c₁) and the codomain absorption never touch the measure, so ∣red∣ is a clean
--   WF metric and the recursion is accepted (the Acc argument is the structural
--   decreasing one).
--
--   WHAT REMAINS after termination is solved: the NON-RU-Struct base case —
--   reflecting a `red` (a direct channel-op / leaf / congruence rule) against a
--   merely-≈-related image.  It is isolated here as the hypothesis `Base`.  That
--   hypothesis is exactly the leaf/≋ reflection the reverse simulation cannot
--   supply:
--     • its strict-image form  R ≈ U[P]σ ⇒ R ≡ U[P†]σ  is machine-FALSE at the
--       νφ-comm φ-escape (Simulation.RevUCong.reverse-U-≋-⊥), and
--     • its ε-absorption fallback (P′ = P, Q ≈ U[P]σ) is machine-UNAVAILABLE for
--       a genuine φ-drop (BorrowedCF.Simulation2.Backward.DropNotAdmin:
--       #acq increments, so the drop reduct is not ≈ its redex).
--   So the WF restructure DISCHARGES termination but leaves `Base` — the design-
--   level φ-telescope-aware reverse inversion — as the genuine open obligation.
module BorrowedCF.Simulation2.Backward.UpToPhiEngineWF where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≈-sym; ≈-trans; ≋⇒≈)
open import BorrowedCF.Simulation.RevCongStrong using (∣_∣)
open import BorrowedCF.Context using (Ctx; Struct)
open TP using (_;_⊢ₚ_)

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (≤-refl)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
         {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P) where

  Res : UP.Proc n → Set
  Res Q = Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × Q ≈ U[ P′ ] σ)

  -- The residual base obligation the WF recursion bottoms out at.
  Base : Set
  Base = ∀ {R Q : UP.Proc n} → R ≈ U[ P ] σ → R UR.─→ₚ Q → Res Q

  -- WF-Acc engine on ∣red∣.  Terminating with no TERMINATING pragma.
  eng-acc : Base → ∀ {R Q : UP.Proc n}
          → R ≈ U[ P ] σ → (red : R UR.─→ₚ Q) → Acc _<_ ∣ red ∣ → Res Q
  eng-acc base R≈ (UR.RU-Struct c₁ inner c₂) (acc rs)
    with P′ , steps , Q′≈ ← eng-acc base
           (≈-trans (≈-sym (≋⇒≈ c₁)) R≈) inner (rs {∣ inner ∣} ≤-refl)
    = P′ , steps , ≈-trans (≋⇒≈ (Eq*.symmetric _ c₂)) Q′≈
  eng-acc base R≈ red (acc rs) = base R≈ red

  -- Public entry: seed the accessibility with <-wellFounded.
  eng : Base → ∀ {R Q : UP.Proc n} → R ≈ U[ P ] σ → (red : R UR.─→ₚ Q) → Res Q
  eng base R≈ red = eng-acc base R≈ red (<-wellFounded ∣ red ∣)
