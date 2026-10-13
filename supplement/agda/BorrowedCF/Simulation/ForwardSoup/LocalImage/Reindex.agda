module BorrowedCF.Simulation.ForwardSoup.LocalImage.Reindex where

open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence

open Nat.Variables

private variable n″ : ℕ

reindex-refl :
  {P : Typed.Proc n}
  {channels : Vec (OrientedChannel c) (Translation.channelCount P)}
  {sigma : Translation.Env n (2 *ℕ c)} →
  ImageReindex {P = P} {Q = P} channels channels sigma sigma
reindex-refl = record
  { channelBackward = id
  ; channelForward = id
  ; channel-forward-backward = λ _ → refl
  ; channel-backward-forward = λ _ → refl
  ; channel-entry = λ _ → refl
  ; channel-content = λ _ → refl
  ; threadBackward = id
  ; threadForward = id
  ; thread-forward-backward = λ _ → refl
  ; thread-backward-forward = λ _ → refl
  ; thread-content = λ _ → refl
  }

reindex-sym :
  {P : Typed.Proc n} {Q : Typed.Proc n′}
  {sourceChannels : Vec (OrientedChannel c) (Translation.channelCount P)}
  {targetChannels : Vec (OrientedChannel c) (Translation.channelCount Q)}
  {sourceEnv : Translation.Env n (2 *ℕ c)}
  {targetEnv : Translation.Env n′ (2 *ℕ c)} →
  ImageReindex {P = P} {Q = Q}
    sourceChannels targetChannels sourceEnv targetEnv →
  ImageReindex {P = Q} {Q = P}
    targetChannels sourceChannels targetEnv sourceEnv
reindex-sym {P = P} {sourceChannels = sourceChannels}
  {sourceEnv = sourceEnv} reindex = record
  { channelBackward = channelForward reindex
  ; channelForward = channelBackward reindex
  ; channel-forward-backward = channel-backward-forward reindex
  ; channel-backward-forward = channel-forward-backward reindex
  ; channel-entry = λ i →
      sym (channel-entry reindex (channelForward reindex i) ■
           cong (physicalChannel ∘ lookup sourceChannels)
             (channel-backward-forward reindex i))
  ; channel-content = λ i →
      sym (channel-content reindex (channelForward reindex i)) ■
      cong (lookup (proj₁ (flattenOriented P sourceChannels sourceEnv)))
        (channel-backward-forward reindex i)
  ; threadBackward = threadForward reindex
  ; threadForward = threadBackward reindex
  ; thread-forward-backward = thread-backward-forward reindex
  ; thread-backward-forward = thread-forward-backward reindex
  ; thread-content = λ i →
      sym (thread-content reindex (threadForward reindex i)) ■
      cong (lookup (proj₂ (flattenOriented P sourceChannels sourceEnv)))
        (thread-backward-forward reindex i)
  }

reindex-trans :
  {P : Typed.Proc n} {Q : Typed.Proc n′} {R : Typed.Proc n″}
  {channelsP : Vec (OrientedChannel c) (Translation.channelCount P)}
  {channelsQ : Vec (OrientedChannel c) (Translation.channelCount Q)}
  {channelsR : Vec (OrientedChannel c) (Translation.channelCount R)}
  {envP : Translation.Env n (2 *ℕ c)}
  {envQ : Translation.Env n′ (2 *ℕ c)}
  {envR : Translation.Env n″ (2 *ℕ c)} →
  ImageReindex {P = P} {Q = Q} channelsP channelsQ envP envQ →
  ImageReindex {P = Q} {Q = R} channelsQ channelsR envQ envR →
  ImageReindex {P = P} {Q = R} channelsP channelsR envP envR
reindex-trans first second = record
  { channelBackward = channelBackward first ∘ channelBackward second
  ; channelForward = channelForward second ∘ channelForward first
  ; channel-forward-backward = λ i →
      cong (channelForward second)
        (channel-forward-backward first (channelBackward second i)) ■
      channel-forward-backward second i
  ; channel-backward-forward = λ i →
      cong (channelBackward first)
        (channel-backward-forward second (channelForward first i)) ■
      channel-backward-forward first i
  ; channel-entry = λ i →
      channel-entry second i ■
      channel-entry first (channelBackward second i)
  ; channel-content = λ i →
      channel-content first (channelBackward second i) ■
      channel-content second i
  ; threadBackward = threadBackward first ∘ threadBackward second
  ; threadForward = threadForward second ∘ threadForward first
  ; thread-forward-backward = λ i →
      cong (threadForward second)
        (thread-forward-backward first (threadBackward second i)) ■
      thread-forward-backward second i
  ; thread-backward-forward = λ i →
      cong (threadBackward first)
        (thread-backward-forward second (threadForward first i)) ■
      thread-backward-forward first i
  ; thread-content = λ i →
      thread-content first (threadBackward second i) ■
      thread-content second i
  }
