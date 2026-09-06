module BorrowedCF.TypedEq where

open import BorrowedCF.Prelude
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)
open import BorrowedCF.Processes.Typed using (Proc; _≋_; _;_⊢ₚ_)
open import BorrowedCF.Reduction.Base using (ChanCx)

open Nat.Variables

variable
  Γ : Ctx n
  γ : Struct n
  P Q : Proc n

-- Compatibility interface for clients written before the congruence-typing
-- proof moved to BorrowedCF.Processes.Congruence.
⊢-≋ : ChanCx Γ → P ≋ Q → Γ ; γ ⊢ₚ P → Γ ; γ ⊢ₚ Q
⊢-≋ Γ-S e p = Γ-S / p ⊢-≋ e
