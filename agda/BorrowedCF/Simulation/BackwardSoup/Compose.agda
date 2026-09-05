-- | Compose exact reflection with slot-renumbering bisimulation.
module BorrowedCF.Simulation.BackwardSoup.Compose where

open import BorrowedCF.Prelude

open import BorrowedCF.Simulation.BackwardSoup.Statement
  using ( Backward-Sim; Slot-Bisim
        ; ≈ˢ-sym; ≈ˢ-trans)
open import BorrowedCF.Simulation.BackwardSoup.Main
  using (Backward-Core)

backward-sim-from : Slot-Bisim → Backward-Core → Backward-Sim
backward-sim-from slot-bisim core ⊢P image imageEq soupRed
  with slot-bisim (≈ˢ-sym imageEq) soupRed
... | D′ , soupRed′ , targetEq
  with core ⊢P image soupRed′
... | P′ , sourceRed , C₀′ , image′ , imageEq′ =
  P′ , sourceRed , C₀′ , image′ ,
  ≈ˢ-trans imageEq′ (≈ˢ-sym targetEq)
