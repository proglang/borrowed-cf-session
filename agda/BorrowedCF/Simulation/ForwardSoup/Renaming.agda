module BorrowedCF.Simulation.ForwardSoup.Renaming where

open import Data.Nat.ListAction using (sum)
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Terms.Base as Source

open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (channelCount-rename; processCount-rename)

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

cast-split :
  {a a′ b b′ : ℕ}
  (left : a ≡ a′) (right : b ≡ b′)
  (xs : Vec A (a + b)) →
  V.cast (cong₂ _+_ left right) xs ≡
  V.cast left (V.take a xs) V.++ V.cast right (V.drop a xs)
cast-split {a = a} refl refl xs =
  VecP.cast-is-id refl xs ■
  sym (V.take++drop≡id a xs) ■
  cong₂ V._++_
    (sym (VecP.cast-is-id refl (V.take a xs)))
    (sym (VecP.cast-is-id refl (V.drop a xs)))

cast-cons :
  {a b : ℕ} (equal : a ≡ b) (x : A) (xs : Vec A a) →
  V.cast (cong suc equal) (x ∷ xs) ≡ x ∷ V.cast equal xs
cast-cons refl x xs =
  VecP.cast-is-id refl (x ∷ xs) ■
  cong (x ∷_) (sym (VecP.cast-is-id refl xs))

transportChannels-cast :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′)
  (xs : Vec A (Translation.channelCount (P Typed.⋯ₚ ρ))) →
  transportChannels P ρ xs ≡
  V.cast (channelCount-rename P ρ) xs
transportChannels-cast (Typed.⟪ e ⟫) ρ [] =
  sym (VecP.cast-is-id refl [])
transportChannels-cast (P Typed.∥ Q) ρ xs =
  cong₂ V._++_
    (transportChannels-cast P ρ
      (V.take (Translation.channelCount (P Typed.⋯ₚ ρ)) xs))
    (transportChannels-cast Q ρ
      (V.drop (Translation.channelCount (P Typed.⋯ₚ ρ)) xs)) ■
  sym (cast-split
    (channelCount-rename P ρ) (channelCount-rename Q ρ) xs)
transportChannels-cast (Typed.ν B₁ B₂ P) ρ (x ∷ xs) =
  cong (x ∷_) (transportChannels-cast P
    (Source._↑*_ ρ (sum B₁ + sum B₂)) xs) ■
  sym (cast-cons
    (channelCount-rename P (Source._↑*_ ρ (sum B₁ + sum B₂)))
    x xs)

transportProcesses-cast :
  (P : Typed.Proc n) (ρ : 𝔽 n → 𝔽 n′)
  (xs : Vec A (Translation.processCount (P Typed.⋯ₚ ρ))) →
  transportProcesses P ρ xs ≡
  V.cast (processCount-rename P ρ) xs
transportProcesses-cast (Typed.⟪ e ⟫) ρ xs =
  sym (VecP.cast-is-id refl xs)
transportProcesses-cast (P Typed.∥ Q) ρ xs =
  cong₂ V._++_
    (transportProcesses-cast P ρ
      (V.take (Translation.processCount (P Typed.⋯ₚ ρ)) xs))
    (transportProcesses-cast Q ρ
      (V.drop (Translation.processCount (P Typed.⋯ₚ ρ)) xs)) ■
  sym (cast-split
    (processCount-rename P ρ) (processCount-rename Q ρ) xs)
transportProcesses-cast (Typed.ν B₁ B₂ P) ρ xs =
  transportProcesses-cast P
    (Source._↑*_ ρ (sum B₁ + sum B₂)) xs
