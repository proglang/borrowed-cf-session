-- HISTORICAL: this file held a machine-checked COUNTEREXAMPLE showing the forward
-- simulation FAILED for R-Drop with b1>=1 -- via skip-padding (a <skip> borrow after
-- the dropped <ret>), making the only untyped drop step (RU-Drop) overshoot the
-- junction flag drop->acq. That bug is FIXED on main by commit ab6faf5 ("BindCtx':
-- the session may never become Skips while variables remain to be bound"), which adds
-- (! Skips s) to BindCtx' cons. The counterexample is now VACUOUS: skip-padding is
-- impossible, so the b1>=1 R-Drop redex is untypeable and R-Drop closes at b1=0 via
-- RU-Drop. The original counterexample is preserved in git history (commit 49f70ba).
module BorrowedCF.Simulation2.DropAcqCounter where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed
open import Data.Empty using (⊥)

-- The fix, machine-checked: no borrow can be peeled from an all-skip session, so
-- skip-padding (the basis of the old R-Drop b1>=1 counterexample) is impossible.
no-skip-pad : ∀ {b} {Γ} → BindCtx′ skip (suc b) Γ → ⊥
no-skip-pad (cons ¬Ss _ _ _) = ¬Ss skip
