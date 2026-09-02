-- Frame lemmas for the phi-separation invariant.
--
-- `Separated` says that the environment and the ambient threads mention `phi`
-- only on ambient channels.  When the simulation descends into a restriction
-- or into one side of a parallel composition, the ambient sets grow by the
-- resources the *other* side owns.  The two lemmas below re-establish
-- `Separated` for the enlarged ambient sets.
module BorrowedCF.Simulation.ForwardSoup.LocalImage.SeparationFrame where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
  using (flatten-par-threads)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Descending under a restriction

-- The binder environment installed by `ν` only mentions `phi` on the two
-- endpoints of the newly bound channel, so it is separated once that channel
-- is added to the ambient set.
separated-bind :
  {B₁ B₂ : Typed.BindGroup} {channel : OrientedChannel n}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  Separated sigma ambientChannel ambientThread C →
  Separated (bindEnv B₁ B₂ channel sigma)
    (ambientChannel ∪ᵖ singletonᵖ (physicalChannel channel))
    ambientThread C
separated-bind {n = n} {B₁ = B₁} {B₂ = B₂} {channel = channel}
  {sigma = sigma} {ambientChannel = aC} separated = record
  { env-separated =
      ++ₛ-phiFree (sum B₁ + sum B₂)
        (envLeft Translation.++ₛ envRight) sigma
        (++ₛ-phiFree (sum B₁) envLeft envRight envLeft-free envRight-free)
        (λ x → phiFree-mono (λ _ → inj₁) (env-separated separated x))
  ; thread-separated = λ j ambient →
      phiFree-mono (λ _ → inj₁) (thread-separated separated j ambient)
  }
  where
  aC′ : 𝔽 n → Set
  aC′ = aC ∪ᵖ singletonᵖ (physicalChannel channel)

  endpointLeft : 𝔽 (2 *ℕ n)
  endpointLeft = physicalEndpoint channel 0F

  endpointRight : 𝔽 (2 *ℕ n)
  endpointRight = physicalEndpoint channel 1F

  envLeft : Translation.Env (sum B₁) (2 *ℕ n)
  envLeft =
    proj₁ (Translation.UB[ B₁ ] endpointLeft
            (SoupTerm.* , endpointLeft , SoupTerm.*))

  envRight : Translation.Env (sum B₂) (2 *ℕ n)
  envRight =
    proj₁ (Translation.UB[ B₂ ] endpointRight
            (SoupTerm.* , endpointRight , SoupTerm.*))

  -- A channel outside the enlarged ambient set is in particular not the
  -- channel bound here, so its endpoints differ from both binder endpoints.
  apart :
    (i : 𝔽 n) (side : 𝔽 2) → ¬ aC′ i → (s : 𝔽 2) →
    Soup.endpoint i side ≢ physicalEndpoint channel s
  apart i side ¬ambient s equal =
    ¬ambient (inj₂ (sym (endpoint-channel-injective equal)))

  envLeft-free : ∀ y → PhiFreeFor aC′ (envLeft y)
  envLeft-free y i side slot ¬ambient =
    UB-phiFree-init B₁ (Soup.endpoint i side) endpointLeft slot
      (apart i side ¬ambient 0F) y

  envRight-free : ∀ y → PhiFreeFor aC′ (envRight y)
  envRight-free y i side slot ¬ambient =
    UB-phiFree-init B₂ (Soup.endpoint i side) endpointRight slot
      (apart i side ¬ambient 1F) y

------------------------------------------------------------------------
-- Descending into one side of a parallel composition

-- Focusing on `P` inside `P ∥ Q` hands `Q`'s channels and threads to the
-- frame; the threads `Q` contributes are phi-free for the enlarged ambient
-- channel set by the scoping lemma.
separated-par-left :
  {P Q : Typed.Proc k}
  {logicalChannels :
    Vec (OrientedChannel n) (Translation.channelCount (P Typed.∥ Q))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  Separated sigma ambientChannel ambientThread C →
  (image : LocalImage (P Typed.∥ Q) logicalChannels sigma
             ambientChannel ambientThread C) →
  Separated sigma
    (ambientChannel ∪ᵖ
      ownedChannels (V.drop (Translation.channelCount P) logicalChannels))
    (ambientThread ∪ᵖ
      ownedThreads
        (threadEmbedding image ∘ (Translation.processCount P ↑ʳ_)))
    C
separated-par-left {n = n} {m = m} {P = P} {Q = Q}
  {logicalChannels = logicalChannels} {sigma = sigma}
  {ambientChannel = aC} {C = C} separated image = record
  { env-separated = λ x →
      phiFree-mono (λ _ → inj₁) (env-separated separated x)
  ; thread-separated = λ where
      j (inj₁ ambient) →
        phiFree-mono (λ _ → inj₁) (thread-separated separated j ambient)
      j (inj₂ (j′ , embedded)) → owned-free j j′ embedded
  }
  where
  processCountP : ℕ
  processCountP = Translation.processCount P

  channelCountP : ℕ
  channelCountP = Translation.channelCount P

  channelsQ : Vec (OrientedChannel n) (Translation.channelCount Q)
  channelsQ = V.drop channelCountP logicalChannels

  aC′ : 𝔽 n → Set
  aC′ = aC ∪ᵖ ownedChannels channelsQ

  threadsP : Vec (Soup.Thread n) (Translation.processCount P)
  threadsP =
    proj₂ (flattenOriented P (V.take channelCountP logicalChannels) sigma)

  threadsQ : Vec (Soup.Thread n) (Translation.processCount Q)
  threadsQ = proj₂ (flattenOriented Q channelsQ sigma)

  threadsQ-free : ∀ i → PhiFreeFor aC′ (lookup threadsQ i)
  threadsQ-free =
    flatten-phiFree Q channelsQ sigma
      (λ y → phiFree-mono (λ _ → inj₁) (env-separated separated y))
      (λ i → inj₂ (i , refl))

  owned-free :
    (j : 𝔽 m) (j′ : 𝔽 (Translation.processCount Q)) →
    threadEmbedding image (processCountP ↑ʳ j′) ≡ just j →
    PhiFreeFor aC′ (lookup (Soup.threads C) j)
  owned-free j j′ embedded
    with live-thread image (processCountP ↑ʳ j′)
  ... | omitted slotEq _ with () ← sym embedded ■ slotEq
  owned-free j j′ embedded
    | present l slotEq liveEq =
    subst (PhiFreeFor aC′) (sym threadEq) (threadsQ-free j′)
    where
    threadEq : lookup (Soup.threads C) j ≡ lookup threadsQ j′
    threadEq =
      cong (lookup (Soup.threads C))
        (just-injective (sym embedded ■ slotEq)) ■
      liveEq ■
      cong (λ xs → lookup xs (processCountP ↑ʳ j′))
        (flatten-par-threads P Q logicalChannels sigma) ■
      V.lookup-++ʳ threadsP threadsQ j′

-- The mirror image: focusing on `Q` hands `P`'s resources to the frame.
separated-par-right :
  {P Q : Typed.Proc k}
  {logicalChannels :
    Vec (OrientedChannel n) (Translation.channelCount (P Typed.∥ Q))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  Separated sigma ambientChannel ambientThread C →
  (image : LocalImage (P Typed.∥ Q) logicalChannels sigma
             ambientChannel ambientThread C) →
  Separated sigma
    (ambientChannel ∪ᵖ
      ownedChannels (V.take (Translation.channelCount P) logicalChannels))
    (ambientThread ∪ᵖ
      ownedThreads
        (threadEmbedding image ∘ (_↑ˡ Translation.processCount Q)))
    C
separated-par-right {n = n} {m = m} {P = P} {Q = Q}
  {logicalChannels = logicalChannels} {sigma = sigma}
  {ambientChannel = aC} {C = C} separated image = record
  { env-separated = λ x →
      phiFree-mono (λ _ → inj₁) (env-separated separated x)
  ; thread-separated = λ where
      j (inj₁ ambient) →
        phiFree-mono (λ _ → inj₁) (thread-separated separated j ambient)
      j (inj₂ (j′ , embedded)) → owned-free j j′ embedded
  }
  where
  processCountQ : ℕ
  processCountQ = Translation.processCount Q

  channelCountP : ℕ
  channelCountP = Translation.channelCount P

  channelsP : Vec (OrientedChannel n) (Translation.channelCount P)
  channelsP = V.take channelCountP logicalChannels

  aC′ : 𝔽 n → Set
  aC′ = aC ∪ᵖ ownedChannels channelsP

  threadsP : Vec (Soup.Thread n) (Translation.processCount P)
  threadsP = proj₂ (flattenOriented P channelsP sigma)

  threadsQ : Vec (Soup.Thread n) (Translation.processCount Q)
  threadsQ =
    proj₂ (flattenOriented Q (V.drop channelCountP logicalChannels) sigma)

  threadsP-free : ∀ i → PhiFreeFor aC′ (lookup threadsP i)
  threadsP-free =
    flatten-phiFree P channelsP sigma
      (λ y → phiFree-mono (λ _ → inj₁) (env-separated separated y))
      (λ i → inj₂ (i , refl))

  owned-free :
    (j : 𝔽 m) (j′ : 𝔽 (Translation.processCount P)) →
    threadEmbedding image (j′ ↑ˡ processCountQ) ≡ just j →
    PhiFreeFor aC′ (lookup (Soup.threads C) j)
  owned-free j j′ embedded
    with live-thread image (j′ ↑ˡ processCountQ)
  ... | omitted slotEq _ with () ← sym embedded ■ slotEq
  owned-free j j′ embedded
    | present l slotEq liveEq =
    subst (PhiFreeFor aC′) (sym threadEq) (threadsP-free j′)
    where
    threadEq : lookup (Soup.threads C) j ≡ lookup threadsP j′
    threadEq =
      cong (lookup (Soup.threads C))
        (just-injective (sym embedded ■ slotEq)) ■
      liveEq ■
      cong (λ xs → lookup xs (j′ ↑ˡ processCountQ))
        (flatten-par-threads P Q logicalChannels sigma) ■
      V.lookup-++ˡ threadsP threadsQ j′
