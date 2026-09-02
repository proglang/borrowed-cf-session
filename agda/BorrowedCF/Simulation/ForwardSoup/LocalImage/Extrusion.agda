-- Scope extrusion for local images.
--
-- `ν-ext′ : P ∥ ν B₁ B₂ Q ≋′ ν B₁ B₂ ((P ⋯ₚ weaken* (sum B₁ + sum B₂)) ∥ Q)`
-- moves the restriction outwards.  Physically nothing happens: the same
-- channels and the same threads are produced, only the indices are permuted
-- (the restricted channel migrates from the middle of the channel vector to
-- its front) and the left component is reindexed along the weakening.  This
-- module builds the corresponding `ImageReindex` and transports local images
-- in both directions.
module BorrowedCF.Simulation.ForwardSoup.LocalImage.Extrusion where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (bindChannel; bindEnv)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Reindex
  using (reindex-sym)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Renaming
  using (renaming-reindex)
open import BorrowedCF.Simulation.ForwardSoup.Renaming
  using (untransportChannels)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupʳ)

open Nat.Variables
open Fin.Patterns

private
  variable
    A : Set
    b o : ℕ

  cons-head-tail :
    {q : ℕ} (xs : Vec A (suc q)) → V.head xs ∷ V.tail xs ≡ xs
  cons-head-tail (x ∷ xs) = refl

------------------------------------------------------------------------
-- The renaming used by `ν-ext′` and its environment coherence

extrusionRenaming :
  (B₁ B₂ : Typed.BindGroup) → 𝔽 n → 𝔽 (sum B₁ + sum B₂ + n)
extrusionRenaming B₁ B₂ = Source.weaken* ⦃ Source.Kᵣ ⦄ (sum B₁ + sum B₂)

-- Weakening past a block of binders is exactly the right injection into an
-- environment extended by that block.
weaken*-coherent :
  (bound : Translation.Env b o) (sigma : Translation.Env n o) (x : 𝔽 n) →
  (bound Translation.++ₛ sigma) (Source.weaken* ⦃ Source.Kᵣ ⦄ b x) ≡ sigma x
weaken*-coherent {b = b} bound sigma x =
  cong (bound Translation.++ₛ sigma) (Source.weaken*~wkˡ ⦃ Source.Kᵣ ⦄ b x) ■
  ++ₛ-lookupʳ bound sigma x

------------------------------------------------------------------------
-- The channel vector of the extruded process

-- `lcP ++ (channel ∷ lcQ)  ↦  channel ∷ (lcP ++ lcQ)`, with the left block
-- transported along the weakening.
extrusionChannels :
  (B₁ B₂ : Typed.BindGroup) (P : Typed.Proc n)
  (Q : Typed.Proc (sum B₁ + sum B₂ + n)) →
  Vec (OrientedChannel c)
    (Translation.channelCount (P Typed.∥ Typed.ν B₁ B₂ Q)) →
  Vec (OrientedChannel c)
    (Translation.channelCount
      (Typed.ν B₁ B₂
        ((P Typed.⋯ₚ extrusionRenaming B₁ B₂) Typed.∥ Q)))
extrusionChannels B₁ B₂ P Q logicalChannels =
  V.head (V.drop (Translation.channelCount P) logicalChannels) ∷
  (untransportChannels P (extrusionRenaming B₁ B₂)
     (V.take (Translation.channelCount P) logicalChannels)
   V.++ V.tail (V.drop (Translation.channelCount P) logicalChannels))

------------------------------------------------------------------------
-- The reindexing

private
  module Extrusion
    {n c : ℕ}
    (B₁ B₂ : Typed.BindGroup)
    (P : Typed.Proc n) (Q : Typed.Proc (sum B₁ + sum B₂ + n))
    (logicalChannels : Vec (OrientedChannel c)
      (Translation.channelCount (P Typed.∥ Typed.ν B₁ B₂ Q)))
    (sigma : Translation.Env n (2 *ℕ c))
    where

    rho : 𝔽 n → 𝔽 (sum B₁ + sum B₂ + n)
    rho = extrusionRenaming B₁ B₂

    renamedP : Typed.Proc (sum B₁ + sum B₂ + n)
    renamedP = P Typed.⋯ₚ rho

    sourceProcess : Typed.Proc n
    sourceProcess = P Typed.∥ Typed.ν B₁ B₂ Q

    targetProcess : Typed.Proc n
    targetProcess = Typed.ν B₁ B₂ (renamedP Typed.∥ Q)

    channelCountP = Translation.channelCount P
    channelCountRen = Translation.channelCount renamedP
    channelCountQ = Translation.channelCount Q
    processCountP = Translation.processCount P
    processCountRen = Translation.processCount renamedP
    processCountQ = Translation.processCount Q

    ------------------------------------------------------------------
    -- Splitting the source channel vector

    channelsP : Vec (OrientedChannel c) channelCountP
    channelsP = V.take channelCountP logicalChannels

    restChannels : Vec (OrientedChannel c) (suc channelCountQ)
    restChannels = V.drop channelCountP logicalChannels

    headChannel : OrientedChannel c
    headChannel = V.head restChannels

    tailChannels : Vec (OrientedChannel c) channelCountQ
    tailChannels = V.tail restChannels

    restEq : headChannel ∷ tailChannels ≡ restChannels
    restEq = cons-head-tail restChannels

    lookup-rest :
      (i : 𝔽 (suc channelCountQ)) →
      lookup restChannels i ≡ lookup (headChannel ∷ tailChannels) i
    lookup-rest i = cong (λ xs → lookup xs i) (sym restEq)

    renamedChannels : Vec (OrientedChannel c) channelCountRen
    renamedChannels = untransportChannels P rho channelsP

    targetChannels :
      Vec (OrientedChannel c) (Translation.channelCount targetProcess)
    targetChannels = headChannel ∷ (renamedChannels V.++ tailChannels)

    ------------------------------------------------------------------
    -- The environment under the restriction

    binderEnv : Translation.Env (sum B₁ + sum B₂) (2 *ℕ c)
    binderEnv =
      proj₁ (Translation.UB[ B₁ ] (physicalEndpoint headChannel 0F)
              (SoupTerm.* , physicalEndpoint headChannel 0F , SoupTerm.*))
      Translation.++ₛ
      proj₁ (Translation.UB[ B₂ ] (physicalEndpoint headChannel 1F)
              (SoupTerm.* , physicalEndpoint headChannel 1F , SoupTerm.*))

    bodyEnv : Translation.Env (sum B₁ + sum B₂ + n) (2 *ℕ c)
    bodyEnv = bindEnv B₁ B₂ headChannel sigma

    -- `P` under `sigma` and `P ⋯ₚ rho` under the extended environment agree.
    bodyReindex :
      ImageReindex {P = P} {Q = renamedP}
        channelsP renamedChannels sigma bodyEnv
    bodyReindex =
      renaming-reindex {P = P} {rho = rho} {sourceChannels = channelsP}
        {sourceEnv = bodyEnv} {targetEnv = sigma}
        (weaken*-coherent binderEnv sigma)

    ------------------------------------------------------------------
    -- Flattened contents on both sides

    sourceChannelTerms = proj₁ (flattenOriented sourceProcess logicalChannels sigma)
    sourceThreadTerms = proj₂ (flattenOriented sourceProcess logicalChannels sigma)
    targetChannelTerms = proj₁ (flattenOriented targetProcess targetChannels sigma)
    targetThreadTerms = proj₂ (flattenOriented targetProcess targetChannels sigma)

    partChannelsP = proj₁ (flattenOriented P channelsP sigma)
    partThreadsP = proj₂ (flattenOriented P channelsP sigma)
    partChannelsRen = proj₁ (flattenOriented renamedP renamedChannels bodyEnv)
    partThreadsRen = proj₂ (flattenOriented renamedP renamedChannels bodyEnv)
    partChannelsQ = proj₁ (flattenOriented Q tailChannels bodyEnv)
    partThreadsQ = proj₂ (flattenOriented Q tailChannels bodyEnv)

    nuChannelEq :
      proj₁ (flattenOriented (Typed.ν B₁ B₂ Q) restChannels sigma) ≡
      bindChannel B₁ B₂ headChannel ∷ partChannelsQ
    nuChannelEq =
      cong (λ xs → proj₁ (flattenOriented (Typed.ν B₁ B₂ Q) xs sigma))
        (sym restEq)

    nuThreadEq :
      proj₂ (flattenOriented (Typed.ν B₁ B₂ Q) restChannels sigma) ≡
      partThreadsQ
    nuThreadEq =
      cong (λ xs → proj₂ (flattenOriented (Typed.ν B₁ B₂ Q) xs sigma))
        (sym restEq)

    sourceChannelEq :
      sourceChannelTerms ≡
      partChannelsP V.++ (bindChannel B₁ B₂ headChannel ∷ partChannelsQ)
    sourceChannelEq =
      flatten-par-channels P (Typed.ν B₁ B₂ Q) logicalChannels sigma ■
      cong (partChannelsP V.++_) nuChannelEq

    sourceThreadEq :
      sourceThreadTerms ≡ partThreadsP V.++ partThreadsQ
    sourceThreadEq =
      flatten-par-threads P (Typed.ν B₁ B₂ Q) logicalChannels sigma ■
      cong (partThreadsP V.++_) nuThreadEq

    targetChannelEq :
      targetChannelTerms ≡
      bindChannel B₁ B₂ headChannel ∷ (partChannelsRen V.++ partChannelsQ)
    targetChannelEq =
      cong (bindChannel B₁ B₂ headChannel ∷_)
        (flatten-par-channels renamedP Q
           (renamedChannels V.++ tailChannels) bodyEnv ■
         cong₂ V._++_
           (cong (λ xs → proj₁ (flattenOriented renamedP xs bodyEnv))
             (take-++ˡ renamedChannels tailChannels))
           (cong (λ xs → proj₁ (flattenOriented Q xs bodyEnv))
             (drop-++ˡ renamedChannels tailChannels)))

    targetThreadEq :
      targetThreadTerms ≡ partThreadsRen V.++ partThreadsQ
    targetThreadEq =
      flatten-par-threads renamedP Q
        (renamedChannels V.++ tailChannels) bodyEnv ■
      cong₂ V._++_
        (cong (λ xs → proj₂ (flattenOriented renamedP xs bodyEnv))
          (take-++ˡ renamedChannels tailChannels))
        (cong (λ xs → proj₂ (flattenOriented Q xs bodyEnv))
          (drop-++ˡ renamedChannels tailChannels))

    ------------------------------------------------------------------
    -- Channel index bijection

    channelBackTail :
      𝔽 channelCountRen ⊎ 𝔽 channelCountQ →
      𝔽 (channelCountP + suc channelCountQ)
    channelBackTail =
      [ (λ i → channelBackward bodyReindex i ↑ˡ suc channelCountQ)
      , (λ i → channelCountP ↑ʳ suc i) ]′

    channelBack :
      𝔽 (suc (channelCountRen + channelCountQ)) →
      𝔽 (channelCountP + suc channelCountQ)
    channelBack zero = channelCountP ↑ʳ zero
    channelBack (suc i) = channelBackTail (Fin.splitAt channelCountRen i)

    channelForwardNu :
      𝔽 (suc channelCountQ) → 𝔽 (suc (channelCountRen + channelCountQ))
    channelForwardNu zero = zero
    channelForwardNu (suc i) = suc (channelCountRen ↑ʳ i)

    channelForwardParts :
      𝔽 channelCountP ⊎ 𝔽 (suc channelCountQ) →
      𝔽 (suc (channelCountRen + channelCountQ))
    channelForwardParts =
      [ (λ i → suc (channelForward bodyReindex i ↑ˡ channelCountQ))
      , channelForwardNu ]′

    channelFwd :
      𝔽 (channelCountP + suc channelCountQ) →
      𝔽 (suc (channelCountRen + channelCountQ))
    channelFwd j = channelForwardParts (Fin.splitAt channelCountP j)

    channelFwd-↑ˡ :
      (j : 𝔽 channelCountP) →
      channelFwd (j ↑ˡ suc channelCountQ) ≡
      suc (channelForward bodyReindex j ↑ˡ channelCountQ)
    channelFwd-↑ˡ j =
      cong channelForwardParts
        (Fin.splitAt-↑ˡ channelCountP j (suc channelCountQ))

    channelFwd-↑ʳ :
      (j : 𝔽 (suc channelCountQ)) →
      channelFwd (channelCountP ↑ʳ j) ≡ channelForwardNu j
    channelFwd-↑ʳ j =
      cong channelForwardParts
        (Fin.splitAt-↑ʳ channelCountP (suc channelCountQ) j)

    channelBack-suc :
      (part : 𝔽 channelCountRen ⊎ 𝔽 channelCountQ) →
      channelBack (suc (Fin.join channelCountRen channelCountQ part)) ≡
      channelBackTail part
    channelBack-suc part =
      cong channelBackTail
        (Fin.splitAt-join channelCountRen channelCountQ part)

    channel-fb-split :
      (part : 𝔽 channelCountRen ⊎ 𝔽 channelCountQ) →
      channelFwd (channelBackTail part) ≡
      suc (Fin.join channelCountRen channelCountQ part)
    channel-fb-split (inj₁ i) =
      channelFwd-↑ˡ (channelBackward bodyReindex i) ■
      cong (λ x → suc (x ↑ˡ channelCountQ))
        (channel-forward-backward bodyReindex i)
    channel-fb-split (inj₂ i) = channelFwd-↑ʳ (suc i)

    channel-fb :
      (i : 𝔽 (suc (channelCountRen + channelCountQ))) →
      channelFwd (channelBack i) ≡ i
    channel-fb zero = channelFwd-↑ʳ zero
    channel-fb (suc i) =
      channel-fb-split (Fin.splitAt channelCountRen i) ■
      cong suc (Fin.join-splitAt channelCountRen channelCountQ i)

    channel-bf-split :
      (part : 𝔽 channelCountP ⊎ 𝔽 (suc channelCountQ)) →
      channelBack (channelForwardParts part) ≡
      Fin.join channelCountP (suc channelCountQ) part
    channel-bf-split (inj₁ j) =
      channelBack-suc (inj₁ (channelForward bodyReindex j)) ■
      cong (_↑ˡ suc channelCountQ) (channel-backward-forward bodyReindex j)
    channel-bf-split (inj₂ zero) = refl
    channel-bf-split (inj₂ (suc j)) = channelBack-suc (inj₂ j)

    channel-bf :
      (j : 𝔽 (channelCountP + suc channelCountQ)) →
      channelBack (channelFwd j) ≡ j
    channel-bf j =
      channel-bf-split (Fin.splitAt channelCountP j) ■
      Fin.join-splitAt channelCountP (suc channelCountQ) j

    ------------------------------------------------------------------
    -- Channel entries and contents

    channel-entry-split :
      (part : 𝔽 channelCountRen ⊎ 𝔽 channelCountQ) →
      physicalChannel
        (lookup (renamedChannels V.++ tailChannels)
          (Fin.join channelCountRen channelCountQ part)) ≡
      physicalChannel (lookup logicalChannels (channelBackTail part))
    channel-entry-split (inj₁ i) =
      cong physicalChannel (V.lookup-++ˡ renamedChannels tailChannels i) ■
      channel-entry bodyReindex i ■
      cong physicalChannel
        (lookup-take channelCountP logicalChannels
          (channelBackward bodyReindex i))
    channel-entry-split (inj₂ i) =
      cong physicalChannel (V.lookup-++ʳ renamedChannels tailChannels i) ■
      cong physicalChannel (sym (lookup-rest (suc i))) ■
      cong physicalChannel (lookup-drop channelCountP logicalChannels (suc i))

    channel-entry-field :
      (i : 𝔽 (suc (channelCountRen + channelCountQ))) →
      physicalChannel (lookup targetChannels i) ≡
      physicalChannel (lookup logicalChannels (channelBack i))
    channel-entry-field zero =
      cong physicalChannel
        (sym (lookup-rest zero) ■
         lookup-drop channelCountP logicalChannels zero)
    channel-entry-field (suc i) =
      cong (λ x →
              physicalChannel (lookup (renamedChannels V.++ tailChannels) x))
        (sym (Fin.join-splitAt channelCountRen channelCountQ i)) ■
      channel-entry-split (Fin.splitAt channelCountRen i)

    channel-content-split :
      (part : 𝔽 channelCountRen ⊎ 𝔽 channelCountQ) →
      lookup sourceChannelTerms (channelBackTail part) ≡
      lookup (partChannelsRen V.++ partChannelsQ)
        (Fin.join channelCountRen channelCountQ part)
    channel-content-split (inj₁ i) =
      cong
        (λ xs →
          lookup xs (channelBackward bodyReindex i ↑ˡ suc channelCountQ))
        sourceChannelEq ■
      V.lookup-++ˡ partChannelsP
        (bindChannel B₁ B₂ headChannel ∷ partChannelsQ)
        (channelBackward bodyReindex i) ■
      channel-content bodyReindex i ■
      sym (V.lookup-++ˡ partChannelsRen partChannelsQ i)
    channel-content-split (inj₂ i) =
      cong (λ xs → lookup xs (channelCountP ↑ʳ suc i)) sourceChannelEq ■
      V.lookup-++ʳ partChannelsP
        (bindChannel B₁ B₂ headChannel ∷ partChannelsQ) (suc i) ■
      sym (V.lookup-++ʳ partChannelsRen partChannelsQ i)

    channel-content-field :
      (i : 𝔽 (suc (channelCountRen + channelCountQ))) →
      lookup sourceChannelTerms (channelBack i) ≡ lookup targetChannelTerms i
    channel-content-field zero =
      cong (λ xs → lookup xs (channelCountP ↑ʳ zero)) sourceChannelEq ■
      V.lookup-++ʳ partChannelsP
        (bindChannel B₁ B₂ headChannel ∷ partChannelsQ) zero ■
      sym (cong (λ xs → lookup xs zero) targetChannelEq)
    channel-content-field (suc i) =
      channel-content-split (Fin.splitAt channelCountRen i) ■
      cong (lookup (partChannelsRen V.++ partChannelsQ))
        (Fin.join-splitAt channelCountRen channelCountQ i) ■
      sym (cong (λ xs → lookup xs (suc i)) targetChannelEq)

    ------------------------------------------------------------------
    -- Thread index bijection and contents

    threadBackParts :
      𝔽 processCountRen ⊎ 𝔽 processCountQ →
      𝔽 (processCountP + processCountQ)
    threadBackParts =
      [ (λ i → threadBackward bodyReindex i ↑ˡ processCountQ)
      , (λ i → processCountP ↑ʳ i) ]′

    threadBack :
      𝔽 (processCountRen + processCountQ) →
      𝔽 (processCountP + processCountQ)
    threadBack i = threadBackParts (Fin.splitAt processCountRen i)

    threadFwdParts :
      𝔽 processCountP ⊎ 𝔽 processCountQ →
      𝔽 (processCountRen + processCountQ)
    threadFwdParts =
      [ (λ i → threadForward bodyReindex i ↑ˡ processCountQ)
      , (λ i → processCountRen ↑ʳ i) ]′

    threadFwd :
      𝔽 (processCountP + processCountQ) →
      𝔽 (processCountRen + processCountQ)
    threadFwd j = threadFwdParts (Fin.splitAt processCountP j)

    thread-fb-split :
      (part : 𝔽 processCountRen ⊎ 𝔽 processCountQ) →
      threadFwd (threadBackParts part) ≡
      Fin.join processCountRen processCountQ part
    thread-fb-split (inj₁ i) =
      cong threadFwdParts
        (Fin.splitAt-↑ˡ processCountP
          (threadBackward bodyReindex i) processCountQ) ■
      cong (_↑ˡ processCountQ) (thread-forward-backward bodyReindex i)
    thread-fb-split (inj₂ i) =
      cong threadFwdParts
        (Fin.splitAt-↑ʳ processCountP processCountQ i)

    thread-fb :
      (i : 𝔽 (processCountRen + processCountQ)) →
      threadFwd (threadBack i) ≡ i
    thread-fb i =
      thread-fb-split (Fin.splitAt processCountRen i) ■
      Fin.join-splitAt processCountRen processCountQ i

    thread-bf-split :
      (part : 𝔽 processCountP ⊎ 𝔽 processCountQ) →
      threadBack (threadFwdParts part) ≡
      Fin.join processCountP processCountQ part
    thread-bf-split (inj₁ j) =
      cong threadBackParts
        (Fin.splitAt-↑ˡ processCountRen
          (threadForward bodyReindex j) processCountQ) ■
      cong (_↑ˡ processCountQ) (thread-backward-forward bodyReindex j)
    thread-bf-split (inj₂ j) =
      cong threadBackParts
        (Fin.splitAt-↑ʳ processCountRen processCountQ j)

    thread-bf :
      (j : 𝔽 (processCountP + processCountQ)) →
      threadBack (threadFwd j) ≡ j
    thread-bf j =
      thread-bf-split (Fin.splitAt processCountP j) ■
      Fin.join-splitAt processCountP processCountQ j

    thread-content-split :
      (part : 𝔽 processCountRen ⊎ 𝔽 processCountQ) →
      lookup sourceThreadTerms (threadBackParts part) ≡
      lookup (partThreadsRen V.++ partThreadsQ)
        (Fin.join processCountRen processCountQ part)
    thread-content-split (inj₁ i) =
      cong (λ xs → lookup xs (threadBackward bodyReindex i ↑ˡ processCountQ))
        sourceThreadEq ■
      V.lookup-++ˡ partThreadsP partThreadsQ (threadBackward bodyReindex i) ■
      thread-content bodyReindex i ■
      sym (V.lookup-++ˡ partThreadsRen partThreadsQ i)
    thread-content-split (inj₂ i) =
      cong (λ xs → lookup xs (processCountP ↑ʳ i)) sourceThreadEq ■
      V.lookup-++ʳ partThreadsP partThreadsQ i ■
      sym (V.lookup-++ʳ partThreadsRen partThreadsQ i)

    thread-content-field :
      (i : 𝔽 (processCountRen + processCountQ)) →
      lookup sourceThreadTerms (threadBack i) ≡ lookup targetThreadTerms i
    thread-content-field i =
      thread-content-split (Fin.splitAt processCountRen i) ■
      cong (lookup (partThreadsRen V.++ partThreadsQ))
        (Fin.join-splitAt processCountRen processCountQ i) ■
      sym (cong (λ xs → lookup xs i) targetThreadEq)

    ------------------------------------------------------------------

    reindex :
      ImageReindex {P = sourceProcess} {Q = targetProcess}
        logicalChannels (extrusionChannels B₁ B₂ P Q logicalChannels)
        sigma sigma
    reindex = record
      { channelBackward = channelBack
      ; channelForward = channelFwd
      ; channel-forward-backward = channel-fb
      ; channel-backward-forward = channel-bf
      ; channel-entry = channel-entry-field
      ; channel-content = channel-content-field
      ; threadBackward = threadBack
      ; threadForward = threadFwd
      ; thread-forward-backward = thread-fb
      ; thread-backward-forward = thread-bf
      ; thread-content = thread-content-field
      }

extrusion-reindex :
  (B₁ B₂ : Typed.BindGroup) (P : Typed.Proc n)
  (Q : Typed.Proc (sum B₁ + sum B₂ + n))
  (logicalChannels : Vec (OrientedChannel c)
    (Translation.channelCount (P Typed.∥ Typed.ν B₁ B₂ Q)))
  (sigma : Translation.Env n (2 *ℕ c)) →
  ImageReindex
    {P = P Typed.∥ Typed.ν B₁ B₂ Q}
    {Q = Typed.ν B₁ B₂
          ((P Typed.⋯ₚ extrusionRenaming B₁ B₂) Typed.∥ Q)}
    logicalChannels (extrusionChannels B₁ B₂ P Q logicalChannels)
    sigma sigma
extrusion-reindex B₁ B₂ P Q logicalChannels sigma =
  Extrusion.reindex B₁ B₂ P Q logicalChannels sigma

------------------------------------------------------------------------
-- Transporting local images

extrusion-image :
  {B₁ B₂ : Typed.BindGroup} {P : Typed.Proc n}
  {Q : Typed.Proc (sum B₁ + sum B₂ + n)}
  {logicalChannels : Vec (OrientedChannel c)
    (Translation.channelCount (P Typed.∥ Typed.ν B₁ B₂ Q))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (P Typed.∥ Typed.ν B₁ B₂ Q) logicalChannels sigma
    ambientChannel ambientThread C →
  LocalImage
    (Typed.ν B₁ B₂ ((P Typed.⋯ₚ extrusionRenaming B₁ B₂) Typed.∥ Q))
    (extrusionChannels B₁ B₂ P Q logicalChannels) sigma
    ambientChannel ambientThread C
extrusion-image {B₁ = B₁} {B₂ = B₂} {P = P} {Q = Q}
  {logicalChannels = logicalChannels} {sigma = sigma} image =
  reindex-image (extrusion-reindex B₁ B₂ P Q logicalChannels sigma) image

extrusion-image⁻ :
  {B₁ B₂ : Typed.BindGroup} {P : Typed.Proc n}
  {Q : Typed.Proc (sum B₁ + sum B₂ + n)}
  {logicalChannels : Vec (OrientedChannel c)
    (Translation.channelCount (P Typed.∥ Typed.ν B₁ B₂ Q))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage
    (Typed.ν B₁ B₂ ((P Typed.⋯ₚ extrusionRenaming B₁ B₂) Typed.∥ Q))
    (extrusionChannels B₁ B₂ P Q logicalChannels) sigma
    ambientChannel ambientThread C →
  LocalImage (P Typed.∥ Typed.ν B₁ B₂ Q) logicalChannels sigma
    ambientChannel ambientThread C
extrusion-image⁻ {B₁ = B₁} {B₂ = B₂} {P = P} {Q = Q}
  {logicalChannels = logicalChannels} {sigma = sigma} image =
  reindex-image
    (reindex-sym (extrusion-reindex B₁ B₂ P Q logicalChannels sigma)) image
