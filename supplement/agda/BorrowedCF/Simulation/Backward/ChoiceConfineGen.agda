-- | Generalised (multi-block) ¬Mobile source for the telescoped backward
--   R-Choice confinement.  Twin of ComConfineGen (send/recv-¬mobile): the
--   select/branch channel session is `brn p s₁ s₂`, and a brn-headed session is
--   NEVER ≃ acq ; _ (via the StartsKind head-rigidity of AtomHead —
--   `¬startskind-brn` + `≃-startskind`), hence ¬ Mobile.  This is the brn
--   analogue of `msg ; ≄ acq ;`, established here without needing NoAcq of the
--   (arbitrary) branch continuations.
module BorrowedCF.Simulation.Backward.ChoiceConfineGen where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP
open import BorrowedCF.Simulation.Support.RevGrindA
  using (select-arg-decomp; branch-arg-decomp)
open import BorrowedCF.Simulation.Support.InvFrame using (arg-type)
open import BorrowedCF.Types using (Mobile; mobile-≃)
open import BorrowedCF.Types.Equivalence using (_≃_; ≃-sym; ≃-trans; Atom; atomKind)
open import BorrowedCF.Types.AtomSnoc using (ClosedKind)
open import BorrowedCF.Types.AtomHead
  using (StartsKind; ¬startskind-brn; ≃-startskind)

open Fin.Patterns

-- brn-headed ≄ acq-headed: a bare `brn p s₁ s₂` is never ≃ acq ; s′.
brn-≄acq : ∀ {p : Pol} {s₁ s₂ s′ : 𝕊 0} → brn p s₁ s₂ ≃ acq ; s′ → ⊥
brn-≄acq eq =
  ¬startskind-brn (≃-startskind ClosedKind.acq (≃-sym eq)
    (StartsKind.▸ (StartsKind.here Atom.acq refl)))

-- hence brn-typed channels are non-mobile.
¬mobile-brn : ∀ {p : Pol} {s₁ s₂ : 𝕊 0} → ¬ Mobile ⟨ brn p s₁ s₂ ⟩
¬mobile-brn ⟨ s′ , bnd , eq ⟩ = brn-≄acq eq

-- The select channel of a well-typed select redex is brn-typed, hence ¬ Mobile.
select-¬mobile : ∀ {N} {Γ : Ctx N} {β : Struct N} {x : 𝔽 N} {U ϵ} {i}
  → Γ ; β ⊢ K (`select i) ·¹ (` x) ∶ U ∣ ϵ → ¬ Mobile (lookup Γ x)
select-¬mobile ⊢redex mob
  with _ , _ , _ , _ , _ , brn≃ , ⊢arg ← select-arg-decomp ⊢redex =
  ¬mobile-brn (mobile-≃ (≃-trans (arg-type ⊢arg) (≃-sym brn≃)) mob)

-- The branch channel of a well-typed branch redex is brn-typed, hence ¬ Mobile.
branch-¬mobile : ∀ {N} {Γ : Ctx N} {β : Struct N} {x : 𝔽 N} {U ϵ}
  → Γ ; β ⊢ K `branch ·¹ (` x) ∶ U ∣ ϵ → ¬ Mobile (lookup Γ x)
branch-¬mobile ⊢redex mob
  with _ , _ , _ , _ , _ , brn≃ , ⊢arg ← branch-arg-decomp ⊢redex =
  ¬mobile-brn (mobile-≃ (≃-trans (arg-type ⊢arg) (≃-sym brn≃)) mob)
