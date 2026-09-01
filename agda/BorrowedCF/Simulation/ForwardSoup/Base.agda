module BorrowedCF.Simulation.ForwardSoup.Base where

open import BorrowedCF.Prelude public

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction

open import BorrowedCF.Processes.TranslationSoup public
open import BorrowedCF.Simulation.ForwardSoup.Image public

open Nat.Variables

PackedConfig : Set
PackedConfig = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] Soup.Config n m

pack : Soup.Config n m → PackedConfig
pack {n = n} {m = m} C = n , m , C

StepImage : Typed.Proc 0 → Soup.Config n m → Set
StepImage P′ C =
  Σ[ n′ ∈ ℕ ] Σ[ m′ ∈ ℕ ] Σ[ C′ ∈ Soup.Config n′ m′ ]
    (C SoupReduction.─→ₚ C′) × SoupImage P′ C′
