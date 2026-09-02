module BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame

open Nat.Variables

private
  -- Transport an optional thread image along an equality of expected threads.
  thread-image-cong :
    {threads : Vec (Soup.Thread n) m} {slot : Maybe (𝔽 m)}
    {expected expected′ : Soup.Thread n} →
    expected ≡ expected′ →
    OptionalThreadImage {n = n} threads slot expected →
    OptionalThreadImage {n = n} threads slot expected′
  thread-image-cong refl image = image

  suc≢zero : {a : ℕ} {i : 𝔽 a} → Fin.suc i ≡ Fin.zero → ⊥
  suc≢zero ()

------------------------------------------------------------------------
-- Splitting and joining the binder frame of a restriction.
--
-- The restriction `ν B₁ B₂ P` owns one more physical channel than its body:
-- the head of the logical channel vector.  Moving between the image of the
-- restriction and the image of its body therefore moves that channel between
-- the *owned* and the *ambient* side of the frame, and exposes the physical
-- content of the bound channel as a separate fact.

module _
  {k n m : ℕ}
  {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum B₁ + sum B₂ + k)}
  {channel : OrientedChannel n}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set}
  {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m}
  where

  -- `flattenOriented` reduces on a restriction, so the implicit arguments of
  -- the `flatten-bind-*` lemmas cannot be recovered from their statements.
  -- Fix them once, for the whole frame.
  private
    head-channel =
      flatten-bind-channel {B₁ = B₁} {B₂ = B₂} {P = P} {channel = channel}
        {logicalChannels = logicalChannels} {sigma = sigma}

    tail-channel =
      flatten-bind-channel-suc {B₁ = B₁} {B₂ = B₂} {P = P} {channel = channel}
        {logicalChannels = logicalChannels} {sigma = sigma}

    body-thread =
      flatten-bind-thread {B₁ = B₁} {B₂ = B₂} {P = P} {channel = channel}
        {logicalChannels = logicalChannels} {sigma = sigma}

  ----------------------------------------------------------------------
  -- Splitting.

  res-split-image :
    LocalImage (Typed.ν B₁ B₂ P) (channel ∷ logicalChannels) sigma
      ambientChannel ambientThread C →
    LocalImage P logicalChannels (bindEnv B₁ B₂ channel sigma)
      (ambientChannel ∪ᵖ singletonᵖ (physicalChannel channel))
      ambientThread C
  res-split-image image = record
    { channelEmbedding-injective = λ {i} {j} equal →
        Fin.suc-injective
          (channelEmbedding-injective image {suc i} {suc j} equal)
    ; threadEmbedding = threadEmbedding image
    ; threadEmbedding-injective = threadEmbedding-injective image
    ; channel-not-ambient = λ i →
        λ { (inj₁ ambient) → channel-not-ambient image (suc i) ambient
          ; (inj₂ equal) →
              suc≢zero
                (channelEmbedding-injective image {suc i} {zero} (sym equal))
          }
    ; thread-not-ambient = thread-not-ambient image
    ; live-channel = λ i →
        live-channel image (suc i) ■ tail-channel i
    ; live-thread = λ j →
        thread-image-cong (body-thread j) (live-thread image j)
    ; garbage-channel = λ i outside notAmbient →
        garbage-channel image i
          (λ { zero → λ equal → notAmbient (inj₂ equal)
             ; (suc j) → outside j
             })
          (notAmbient ∘ inj₁)
    ; garbage-thread = garbage-thread image
    }

  -- The physical content of the bound channel.
  res-split-channel :
    LocalImage (Typed.ν B₁ B₂ P) (channel ∷ logicalChannels) sigma
      ambientChannel ambientThread C →
    lookup (Soup.channels C) (physicalChannel channel) ≡
    bindChannel B₁ B₂ channel
  res-split-channel image = live-channel image zero ■ head-channel

  -- The bound channel is not part of the ambient frame; `res-join` needs this
  -- fact back, so it is exported alongside the split.
  res-split-not-ambient :
    LocalImage (Typed.ν B₁ B₂ P) (channel ∷ logicalChannels) sigma
      ambientChannel ambientThread C →
    ¬ ambientChannel (physicalChannel channel)
  res-split-not-ambient image = channel-not-ambient image zero

  res-split :
    LocalImage (Typed.ν B₁ B₂ P) (channel ∷ logicalChannels) sigma
      ambientChannel ambientThread C →
    LocalImage P logicalChannels (bindEnv B₁ B₂ channel sigma)
      (ambientChannel ∪ᵖ singletonᵖ (physicalChannel channel))
      ambientThread C
    × lookup (Soup.channels C) (physicalChannel channel) ≡
      bindChannel B₁ B₂ channel
  res-split image = res-split-image image , res-split-channel image

  ----------------------------------------------------------------------
  -- Joining.

  res-join :
    LocalImage P logicalChannels (bindEnv B₁ B₂ channel sigma)
      (ambientChannel ∪ᵖ singletonᵖ (physicalChannel channel))
      ambientThread C →
    lookup (Soup.channels C) (physicalChannel channel) ≡
    bindChannel B₁ B₂ channel →
    ¬ ambientChannel (physicalChannel channel) →
    LocalImage (Typed.ν B₁ B₂ P) (channel ∷ logicalChannels) sigma
      ambientChannel ambientThread C
  res-join image channelContent channelNotAmbient = record
    { channelEmbedding-injective = λ {i} {j} → injective {i} {j}
    ; threadEmbedding = threadEmbedding image
    ; threadEmbedding-injective = threadEmbedding-injective image
    ; channel-not-ambient =
        λ { zero → channelNotAmbient
          ; (suc i) → λ ambient → channel-not-ambient image i (inj₁ ambient)
          }
    ; thread-not-ambient = thread-not-ambient image
    ; live-channel =
        λ { zero → channelContent ■ sym head-channel
          ; (suc i) → live-channel image i ■ sym (tail-channel i)
          }
    ; live-thread = λ j →
        thread-image-cong (sym (body-thread j)) (live-thread image j)
    ; garbage-channel = λ i outside notAmbient →
        garbage-channel image i
          (λ j → outside (suc j))
          (λ { (inj₁ ambient) → notAmbient ambient
             ; (inj₂ equal) → outside zero equal
             })
    ; garbage-thread = garbage-thread image
    }
    where
    injective :
      {i j : 𝔽 (Translation.channelCount (Typed.ν B₁ B₂ P))} →
      physicalChannel (lookup (channel ∷ logicalChannels) i) ≡
      physicalChannel (lookup (channel ∷ logicalChannels) j) →
      i ≡ j
    injective {zero} {zero} _ = refl
    injective {zero} {suc j} equal =
      ⊥-elim (channel-not-ambient image j (inj₂ equal))
    injective {suc i} {zero} equal =
      ⊥-elim (channel-not-ambient image i (inj₂ (sym equal)))
    injective {suc i} {suc j} equal =
      cong Fin.suc (channelEmbedding-injective image equal)
