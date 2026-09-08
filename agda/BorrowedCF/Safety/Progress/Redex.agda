-- | Single-thread redexes of the process progress theorem (agent G1, wave 2).
--
--   Every lemma here has the same shape: a CLOSED well-typed process presented
--   as `plug ctx ⟪ E [ K c ·¹ w ]* ⟫` with a NON-BLOCKING constant `c` at the
--   hole reduces.  The typed rules of `Reduction/Processes/Typed.agda` fire
--   only on threads that sit as the LEFT component of a `∥` directly under
--   their own binder, so each proof is
--
--     canonical form (`Simulation/BackwardSoup/Canonical.agda`)
--       + `R-Struct` + `red-in-ctx` (`Progress/Redex/Context.agda`).
--
--   `redex-new` and `redex-fork` need neither: `R-New` and `R-Fork` fire on a
--   bare thread, so `red-in-ctx` alone does it.
--
--   `drop` / `discard` live in `Redex/Handles.agda` and `acq` in
--   `Redex/Acq.agda`; this module re-exports them.
module BorrowedCF.Safety.Progress.Redex where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using () renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed using (Proc; ⟪_⟫)
open import BorrowedCF.Reduction.Processes.Typed
  using (_─→ₚ_; R-New; R-Fork; R-LSplit; R-RSplit; R-Struct)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; plug)
open import BorrowedCF.Simulation.BackwardSoup.Position using (resolve)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (CanonSplit; canon-lsplit; canon-rsplit)

open import BorrowedCF.Safety.Progress.Redex.Context public
  using (red-in-ctx; step-in-ctx)
open import BorrowedCF.Safety.Progress.Redex.Located public
  using (∈BC⇒located; ∈AC⇒located; ∈AC⇒located-acq; ∈BCe⇒shape; ∈ACe⇒shape)
open import BorrowedCF.Safety.Progress.Redex.SplitShape using (split-shape)
open import BorrowedCF.Safety.Progress.Redex.Handles public
  using (redex-drop; redex-discard; drop-first-group)
open import BorrowedCF.Safety.Progress.Redex.Acq public
  using ( redex-acq; acqBinderˡ; acqBinderʳ
        ; redex-acq-exposedˡ; redex-acq-exposedʳ; acq-position )

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 1.  `new` and `fork`: no binder involved.

redex-new :
  {k n : ℕ} (ctx : ProcessContext k n) (E : Frame* k) (s : 𝕊 0) →
  Σ[ P′ ∈ Proc n ] plug ctx ⟪ E [ K (`new s) ·¹ * ]* ⟫ ─→ₚ P′
redex-new ctx E s = _ , red-in-ctx ctx (R-New E)

redex-fork :
  {k n : ℕ} (ctx : ProcessContext k n) (E : Frame* k) {e : Tm k} → Value e →
  Σ[ P′ ∈ Proc n ] plug ctx ⟪ E [ K `fork ·¹ e ]* ⟫ ─→ₚ P′
redex-fork ctx E V = _ , red-in-ctx ctx (R-Fork E V)

------------------------------------------------------------------------
-- 2.  `lsplit` / `rsplit`: any position of any group is a split position
--     (`Redex/SplitShape.agda`), so no typing hypothesis is needed either.

redex-lsplit :
  {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (s₀ : 𝕊 0) (x : 𝔽 k) →
  Σ[ P′ ∈ Proc 0 ] plug ctx ⟪ E [ K (`lsplit s₀) ·¹ (` x) ]* ⟫ ─→ₚ P′
redex-lsplit ctx E s₀ x
  with canon-lsplit s₀ E (resolve ctx x) (split-shape (resolve ctx x))
... | cs = _ , R-Struct (CanonSplit.≋-redex cs)
                 (red-in-ctx (CanonSplit.above′ cs)
                   (R-LSplit {s = CanonSplit.sess cs} {E = CanonSplit.E₀ cs}))
                 ≋-refl

redex-rsplit :
  {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (s₀ : 𝕊 0) (x : 𝔽 k) →
  Σ[ P′ ∈ Proc 0 ] plug ctx ⟪ E [ K (`rsplit s₀) ·¹ (` x) ]* ⟫ ─→ₚ P′
redex-rsplit ctx E s₀ x
  with canon-rsplit s₀ E (resolve ctx x) (split-shape (resolve ctx x))
... | cs = _ , R-Struct (CanonSplit.≋-redex cs)
                 (red-in-ctx (CanonSplit.above′ cs)
                   (R-RSplit {s = CanonSplit.sess cs} {E = CanonSplit.E₀ cs}))
                 ≋-refl

