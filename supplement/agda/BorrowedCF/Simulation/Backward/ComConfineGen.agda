-- | Generalised (multi-block) ¬Mobile source for the telescoped backward R-Com /
--   R-Choice confinement.  The singleton flat engines used `¬mobile-block-at`
--   (via `block-NoAcq`), which is FALSE for later blocks (they are acq-factors).
--   Instead we read ¬Mobile straight off the REDEX TYPING: the send/recv channel
--   session is `msg p T`, and `NoAcq (msg …)` ⇒ ¬ Mobile.
module BorrowedCF.Simulation.Backward.ComConfineGen where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2
  using (send-handle-≃msg-app; recv-handle-≃msg-app)
open import BorrowedCF.Simulation.Support.CloseVacuityProbe using (NoAcq; ¬mobile-noAcq)
open import BorrowedCF.Types using (Mobile; mobile-≃)

open Fin.Patterns

-- The send channel of a well-typed send redex is msg-typed, hence NoAcq, hence
-- ¬ Mobile.  (Replaces ¬mobile-block-at, which is unsound for non-front blocks.)
send-¬mobile : ∀ {N} {Γ : Ctx N} {β : Struct N} {ee} {x : 𝔽 N} {U ϵ}
  → Γ ; β ⊢ K `send ·¹ (ee ⊗ (` x)) ∶ U ∣ ϵ → ¬ Mobile (lookup Γ x)
send-¬mobile ⊢redex mob =
  let _ , H≃ = send-handle-≃msg-app ⊢redex
  in ¬mobile-noAcq NoAcq.msg (mobile-≃ H≃ mob)

recv-¬mobile : ∀ {N} {Γ : Ctx N} {β : Struct N} {y : 𝔽 N} {U ϵ}
  → Γ ; β ⊢ K `recv ·¹ (` y) ∶ U ∣ ϵ → ¬ Mobile (lookup Γ y)
recv-¬mobile ⊢redex mob =
  let _ , H≃ = recv-handle-≃msg-app ⊢redex
  in ¬mobile-noAcq NoAcq.msg (mobile-≃ H≃ mob)
