module BorrowedCF.Simulation.ForwardSoup.LocalImage.Renaming where

open import Data.Maybe using (Maybe)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Vec.Properties as VecP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
open import BorrowedCF.Simulation.ForwardSoup.Renaming
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (channelCount-rename; processCount-rename)

open Nat.Variables

rename-image :
  {P : Typed.Proc n} {rho : 𝔽 n → 𝔽 n′}
  {sourceChannels :
    Vec (OrientedChannel c) (Translation.channelCount P)}
  {sourceEnv : Translation.Env n′ (2 *ℕ c)}
  {targetEnv : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  ((x : 𝔽 n) → sourceEnv (rho x) ≡ targetEnv x) →
  LocalImage P sourceChannels targetEnv
    ambientChannel ambientThread C →
  LocalImage (P Typed.⋯ₚ rho)
    (untransportChannels P rho sourceChannels) sourceEnv
    ambientChannel ambientThread C
rename-image {P = P} {rho = rho} {sourceChannels = sourceChannels}
  {sourceEnv = sourceEnv} {targetEnv = targetEnv} coherent image =
  reindex-image reindex image
  where
  targetChannels = untransportChannels P rho sourceChannels
  channelEq = channelCount-rename P rho
  processEq = processCount-rename P rho

  targetChannelTerms =
    proj₁ (flattenOriented (P Typed.⋯ₚ rho) targetChannels sourceEnv)
  sourceChannelTerms =
    proj₁ (flattenOriented P sourceChannels targetEnv)
  targetThreads =
    proj₂ (flattenOriented (P Typed.⋯ₚ rho) targetChannels sourceEnv)
  sourceThreads =
    proj₂ (flattenOriented P sourceChannels targetEnv)

  channelTerms-cast :
    V.cast channelEq targetChannelTerms ≡ sourceChannelTerms
  channelTerms-cast =
    sym (transportChannels-cast P rho targetChannelTerms) ■
    flattenChannels-rename P rho targetChannels sourceEnv targetEnv coherent ■
    cong (λ channels → proj₁ (flattenOriented P channels targetEnv))
      (transportChannels-untransport P rho sourceChannels)

  threadTerms-cast :
    V.cast processEq targetThreads ≡ sourceThreads
  threadTerms-cast =
    sym (transportProcesses-cast P rho targetThreads) ■
    flattenThreads-rename P rho targetChannels sourceEnv targetEnv coherent ■
    cong (λ channels → proj₂ (flattenOriented P channels targetEnv))
      (transportChannels-untransport P rho sourceChannels)

  reindex :
    ImageReindex {P = P} {Q = P Typed.⋯ₚ rho}
      sourceChannels targetChannels targetEnv sourceEnv
  reindex = record
    { channelBackward = Fin.cast channelEq
    ; channelForward = Fin.cast (sym channelEq)
    ; channel-forward-backward =
        Fin.cast-involutive (sym channelEq) channelEq
    ; channel-backward-forward =
        Fin.cast-involutive channelEq (sym channelEq)
    ; channel-entry = λ i → cong physicalChannel
        (VecP.lookup-cast₁ (sym channelEq) sourceChannels i)
    ; channel-content = λ i →
        cong (λ xs → lookup xs (Fin.cast channelEq i))
          (sym channelTerms-cast) ■
        VecP.lookup-cast₁ channelEq targetChannelTerms
          (Fin.cast channelEq i) ■
        cong (lookup targetChannelTerms)
          (Fin.cast-involutive (sym channelEq) channelEq i)
    ; threadBackward = Fin.cast processEq
    ; threadForward = Fin.cast (sym processEq)
    ; thread-forward-backward =
        Fin.cast-involutive (sym processEq) processEq
    ; thread-backward-forward =
        Fin.cast-involutive processEq (sym processEq)
    ; thread-content = λ i →
        cong (λ xs → lookup xs (Fin.cast processEq i))
          (sym threadTerms-cast) ■
        VecP.lookup-cast₁ processEq targetThreads
          (Fin.cast processEq i) ■
        cong (lookup targetThreads)
          (Fin.cast-involutive (sym processEq) processEq i)
    }
