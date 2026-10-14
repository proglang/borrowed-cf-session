module BorrowedCF.Simulation.ForwardSoup.World where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Properties

open Nat.Variables

record GlobalImage
  (P : Typed.Proc 0) {n m : ℕ} (C : Soup.Config n m) : Set where
  field
    logicalChannels :
      Vec (OrientedChannel n) (Translation.channelCount P)

    localImage :
      LocalImage P logicalChannels (λ ())
        (λ _ → ⊥) (λ _ → ⊥) C

open GlobalImage public

initialGlobalImage :
  (P : Typed.Proc 0) →
  GlobalImage P
    (Soup.config
      (proj₁ (Translation.flatten P
        (V.allFin (Translation.channelCount P)) (λ ())))
      (proj₂ (Translation.flatten P
        (V.allFin (Translation.channelCount P)) (λ ()))))
initialGlobalImage P = record
  { logicalChannels =
      V.map forwardChannel (V.allFin (Translation.channelCount P))
  ; localImage = initialLocalImage P
  }

GlobalStepImage :
  Typed.Proc 0 → Soup.Config n m → Set
GlobalStepImage P′ C =
  Σ[ n′ ∈ ℕ ] Σ[ m′ ∈ ℕ ] Σ[ C′ ∈ Soup.Config n′ m′ ]
    (C SoupReduction.─→ₚ C′) × GlobalImage P′ C′
