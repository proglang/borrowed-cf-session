-- Barrel: re-exports the whole Simulation development.
module BorrowedCF.Simulation where

open import BorrowedCF.Simulation.Frames public
open import BorrowedCF.Simulation.SubstLemmas public
open import BorrowedCF.Simulation.BlockSwap public
open import BorrowedCF.Simulation.TranslationProperties public
open import BorrowedCF.Simulation.Flatten public
open import BorrowedCF.Simulation.BlockPermutation public
open import BorrowedCF.Simulation.NuExtrusion public

-- NOTE: BorrowedCF.Simulation.Theorems (U-≋, sim→, U-ν-swap) is checked
-- standalone; it has open holes so cannot be re-exported here.
