module BorrowedCF.Simulation.ForwardSoup.Renaming where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Terms.Base as Source

open Nat.Variables

private variable A : Set

transportChannels :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
  Vec A (Translation.channelCount (P Typed.⋯ₚ ρ)) →
  Vec A (Translation.channelCount P)
transportChannels (Typed.⟪ e ⟫) ρ [] = []
transportChannels (P Typed.∥ Q) ρ xs =
  transportChannels P ρ
    (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) xs) V.++
  transportChannels Q ρ
    (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) xs)
transportChannels (Typed.ν B₁ B₂ P) ρ (x ∷ xs) =
  x ∷ transportChannels P
    (Source._↑*_ ρ (sum B₁ + sum B₂)) xs

transportProcesses :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′) →
  Vec A (Translation.processCount (P Typed.⋯ₚ ρ)) →
  Vec A (Translation.processCount P)
transportProcesses (Typed.⟪ e ⟫) ρ xs = xs
transportProcesses (P Typed.∥ Q) ρ xs =
  transportProcesses P ρ
    (V.take (Translation.processCount (P Typed.⋯ₚ ρ)) xs) V.++
  transportProcesses Q ρ
    (V.drop (Translation.processCount (P Typed.⋯ₚ ρ)) xs)
transportProcesses (Typed.ν B₁ B₂ P) ρ xs =
  transportProcesses P (Source._↑*_ ρ (sum B₁ + sum B₂)) xs
