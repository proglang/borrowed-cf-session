-- Unary fixed-front soup target: complete closed-process simulations.
-- FrontCore supplies normalization, quotient bisimulation and the forward
-- theorem; backward simulation is a restriction of the existing theorem.
module BorrowedCF.Simulation.FrontSoup where

open import BorrowedCF.Prelude
import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.Typed as SourceReduction
open import BorrowedCF.Simulation.FrontCore public
open import BorrowedCF.Simulation.BackwardSoup.Simulation using (backward-sim)

open Typed using (_;_⊢ₚ_)
open Nat.Variables

backward-front : ∀ {P : Typed.Proc 0} {n m n′ m′}
  {C : Soup.Config n m} {C′ : Soup.Config n′ m′} →
  [] ; Context.[] ⊢ₚ P →
  FrontImage P C → FrontStep C C′ →
  Σ[ P′ ∈ Typed.Proc 0 ] (P SourceReduction.─→ₚ P′) × FrontImage P′ C′
backward-front typing (C₀ , image , equivalent) step =
  backward-sim typing image equivalent (underlying step)
