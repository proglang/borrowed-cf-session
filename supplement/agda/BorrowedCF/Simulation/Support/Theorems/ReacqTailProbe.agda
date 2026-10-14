module BorrowedCF.Simulation.Support.Theorems.ReacqTailProbe where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed
open import Data.List using ([]; _∷_)

open Nat.Variables

-- Counterexample to `¬ (BindCtx (acq ; s₂) (c∷Bp) Γ)` when Skips s₂:
-- a SINGLETON re-acquire tail (c∷[]) is `last (BindCtx′ (acq;s₂) …)`, which
-- (having NO ret marker) is INHABITED — a single borrow whose session ≃ acq.
-- s₂ = skip (Skips skip), acq;skip ≃ acq.
reacq-singleton-inhabited :
  BindCtx (acq ; skip) (1 ∷ []) (⟨ acq ⟩ ∷ [])
reacq-singleton-inhabited =
  last (cons acq skip ¬sk ≃-refl (nil skips-skip))
  where
    ¬sk : ¬ Skips (acq ; skip)
    ¬sk (() ; _)
    skips-skip : Skips skip
    skips-skip = skip
