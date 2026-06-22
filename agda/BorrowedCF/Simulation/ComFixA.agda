-- Fix A validation: swapping the R-Com send pair to  (message ⊗ channel)  with the
-- channel endpoint 0F in the CHANNEL slot makes the send thread TYPABLE — the Mobile
-- demand falls on the message (⊤, which IS Mobile), not the channel (⟨msg ‼ ⊤⟩, which
-- is NOT, per ComWitness.¬mobile-send-msg).  Contrast ComWitness.sendExpr (original
-- order) which only typechecks given the impossible Mobile ⟨ msg ‼ ⊤ ⟩.

module BorrowedCF.Simulation.ComFixA where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Simulation.ComWitness using (bodyCtx; gS)

open Fin.Patterns
open Nat.Variables

-- swapped send:  message K `unit : `⊤  (Mobile),  channel ` 0F : ⟨ msg ‼ `⊤ ⟩.
sendExpr-fixed : bodyCtx ; ([] ∥ ([] ∥ (` 0F))) ⊢ K `send · (K `unit ⊗ (` 0F)) ∶ `⊤ ∣ 𝕀
sendExpr-fixed = T-AppLin refl
  (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send `⊤)))
  (T-Pair par (T-Conv ≃-refl ℙ≤ϵ (T-Const `unit)) (T-Conv ≃-refl ℙ≤ϵ (T-Var 0F refl)) par)
