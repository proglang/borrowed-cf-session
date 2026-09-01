module BorrowedCF.Simulation.ForwardSoup.Context.Properties where

open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Context
open import BorrowedCF.Simulation.ForwardSoup.LocalImage

open Nat.Variables

Focus : ℕ → ℕ → ℕ → Set
Focus channelCount arity c =
  Vec (OrientedChannel c) channelCount ×
  Translation.Env arity (2 *ℕ c)

focus :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)) →
  Translation.Env n (2 *ℕ c) →
  Focus (Translation.channelCount P) k c
focus hole P channels sigma = channels , sigma
focus (par context Q) P channels sigma =
  focus context P
    (V.take (Translation.channelCount (plug context P)) channels) sigma
focus (bind B₁ B₂ context) P (channel ∷ channels) sigma
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  focus context P channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma)

focusChannels :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)) →
  Translation.Env n (2 *ℕ c) →
  Vec (OrientedChannel c) (Translation.channelCount P)
focusChannels context P channels sigma =
  proj₁ (focus context P channels sigma)

focusEnv :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P))) →
  Translation.Env n (2 *ℕ c) →
  Translation.Env k (2 *ℕ c)
focusEnv context P channels sigma =
  proj₂ (focus context P channels sigma)

focus-channel :
  (context : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)))
  (sigma : Translation.Env n (2 *ℕ c))
  (i : 𝔽 (Translation.channelCount P)) →
  lookup (proj₁ (flattenOriented (plug context P) channels sigma))
    (channelInContext context P i) ≡
  lookup (proj₁ (flattenOriented P
    (focusChannels context P channels sigma)
    (focusEnv context P channels sigma))) i
focus-channel hole P channels sigma i = refl
focus-channel (par context Q) P channels sigma i
  with flattenOriented (plug context P)
         (V.take (Translation.channelCount (plug context P)) channels) sigma
         in flatP
     | flattenOriented Q
         (V.drop (Translation.channelCount (plug context P)) channels) sigma
         in flatQ
... | channelsP , threadsP | channelsQ , threadsQ =
  V.lookup-++ˡ channelsP channelsQ (channelInContext context P i) ■
  sym (cong
    (λ result → lookup (proj₁ result) (channelInContext context P i))
    flatP) ■
  focus-channel context P
    (V.take (Translation.channelCount (plug context P)) channels) sigma i
focus-channel (bind B₁ B₂ context) P (channel ∷ channels) sigma i
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  focus-channel context P channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma) i

focus-thread :
  (context : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug context P)))
  (sigma : Translation.Env n (2 *ℕ c))
  (i : 𝔽 (Translation.processCount P)) →
  lookup (proj₂ (flattenOriented (plug context P) channels sigma))
    (threadInContext context P i) ≡
  lookup (proj₂ (flattenOriented P
    (focusChannels context P channels sigma)
    (focusEnv context P channels sigma))) i
focus-thread hole P channels sigma i = refl
focus-thread (par context Q) P channels sigma i
  with flattenOriented (plug context P)
         (V.take (Translation.channelCount (plug context P)) channels) sigma
         in flatP
     | flattenOriented Q
         (V.drop (Translation.channelCount (plug context P)) channels) sigma
         in flatQ
... | channelsP , threadsP | channelsQ , threadsQ =
  V.lookup-++ˡ threadsP threadsQ (threadInContext context P i) ■
  sym (cong
    (λ result → lookup (proj₂ result) (threadInContext context P i))
    flatP) ■
  focus-thread context P
    (V.take (Translation.channelCount (plug context P)) channels) sigma i
focus-thread (bind B₁ B₂ context) P (channel ∷ channels) sigma i
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂ =
  focus-thread context P channels
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma) i
