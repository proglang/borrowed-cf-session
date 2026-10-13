-- | Backward simulation for the strict soup target.
module BorrowedCF.Simulation.BackwardSoup.Simulation where

open import BorrowedCF.Simulation.BackwardSoup.Statement
  using (Backward-Sim)
open import BorrowedCF.Simulation.BackwardSoup.Main
  using (backward-core)
open import BorrowedCF.Simulation.BackwardSoup.Compose
  using (backward-sim-from)
open import BorrowedCF.Simulation.BackwardSoup.SlotBisim
  using (slot-bisim)

backward-sim : Backward-Sim
backward-sim = backward-sim-from slot-bisim backward-core
