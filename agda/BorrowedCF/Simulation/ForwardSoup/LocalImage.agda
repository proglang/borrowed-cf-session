module BorrowedCF.Simulation.ForwardSoup.LocalImage where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just; nothing)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open Nat.Variables

variable c : ℕ

data Orientation : Set where
  forward reverse : Orientation

flipOrientation : Orientation → Orientation
flipOrientation forward = reverse
flipOrientation reverse = forward

flipOrientation-involutive :
  (orientation : Orientation) →
  flipOrientation (flipOrientation orientation) ≡ orientation
flipOrientation-involutive forward = refl
flipOrientation-involutive reverse = refl

orientSide : Orientation → 𝔽 2 → 𝔽 2
orientSide forward side = side
orientSide reverse zero = suc zero
orientSide reverse (suc zero) = zero

orientChannel : Orientation → Soup.Channel → Soup.Channel
orientChannel forward channel = channel
orientChannel reverse (open? , leftFlags , rightFlags) =
  open? , rightFlags , leftFlags

OrientedChannel : ℕ → Set
OrientedChannel n = 𝔽 n × Orientation

physicalChannel : OrientedChannel n → 𝔽 n
physicalChannel = proj₁

physicalEndpoint : OrientedChannel n → 𝔽 2 → 𝔽 (2 *ℕ n)
physicalEndpoint (channel , orientation) side =
  Soup.endpoint channel (orientSide orientation side)

flipOrientedChannel : OrientedChannel n → OrientedChannel n
flipOrientedChannel (channel , orientation) =
  channel , flipOrientation orientation

physicalChannel-flip :
  (channel : OrientedChannel n) →
  physicalChannel (flipOrientedChannel channel) ≡ physicalChannel channel
physicalChannel-flip (channel , orientation) = refl

physicalEndpoint-flip-left :
  (channel : OrientedChannel n) →
  physicalEndpoint (flipOrientedChannel channel) zero ≡
  physicalEndpoint channel (suc zero)
physicalEndpoint-flip-left (channel , forward) = refl
physicalEndpoint-flip-left (channel , reverse) = refl

physicalEndpoint-flip-right :
  (channel : OrientedChannel n) →
  physicalEndpoint (flipOrientedChannel channel) (suc zero) ≡
  physicalEndpoint channel zero
physicalEndpoint-flip-right (channel , forward) = refl
physicalEndpoint-flip-right (channel , reverse) = refl

orientChannel-flip :
  (channel : OrientedChannel n) (open? : Bool)
  (leftFlags rightFlags : List Soup.Flag) →
  orientChannel (proj₂ (flipOrientedChannel channel))
    (open? , rightFlags , leftFlags) ≡
  orientChannel (proj₂ channel)
    (open? , leftFlags , rightFlags)
orientChannel-flip (channel , forward) open? leftFlags rightFlags = refl
orientChannel-flip (channel , reverse) open? leftFlags rightFlags = refl

-- Flatten directly into a physical soup namespace.  An orientation records
-- which physical endpoint implements each source endpoint.
flattenOriented :
  (P : Typed.Proc n) →
  Vec (OrientedChannel c) (Translation.channelCount P) →
  Translation.Env n (2 *ℕ c) →
  Vec Soup.Channel (Translation.channelCount P) ×
  Vec (Soup.Thread c) (Translation.processCount P)
flattenOriented (Typed.⟪ e ⟫) [] sigma =
  [] , Translation.T[ e ] sigma ∷ []
flattenOriented (P Typed.∥ Q) channels sigma
  with flattenOriented P (V.take (Translation.channelCount P) channels) sigma
     | flattenOriented Q (V.drop (Translation.channelCount P) channels) sigma
... | channelsP , threadsP | channelsQ , threadsQ =
  channelsP V.++ channelsQ , threadsP V.++ threadsQ
flattenOriented (Typed.ν B₁ B₂ P) (channel ∷ channels) sigma
  with Translation.UB[ B₁ ] (physicalEndpoint channel zero)
         (SoupTerm.* , physicalEndpoint channel zero , SoupTerm.*)
     | Translation.UB[ B₂ ] (physicalEndpoint channel (suc zero))
         (SoupTerm.* , physicalEndpoint channel (suc zero) , SoupTerm.*)
... | sigma₁ , flags₁ | sigma₂ , flags₂
  with flattenOriented P channels
         ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma)
... | channelsP , threadsP =
  orientChannel (proj₂ channel) (true , flags₁ , flags₂) ∷ channelsP ,
  threadsP

LocalOutside : {a b : ℕ} → (𝔽 a → 𝔽 b) → 𝔽 b → Set
LocalOutside embedding i = (k : _) → embedding k ≢ i

OptionalOutside : {a b : ℕ} → (𝔽 a → Maybe (𝔽 b)) → 𝔽 b → Set
OptionalOutside embedding i = (k : _) → embedding k ≢ just i

data OptionalThreadImage
  {n m : ℕ}
  (threads : Vec (Soup.Thread n) m)
  (slot : Maybe (𝔽 m))
  (expected : Soup.Thread n) : Set where
  present :
    (l : 𝔽 m) →
    slot ≡ just l →
    lookup threads l ≡ expected →
    OptionalThreadImage threads slot expected

  omitted :
    slot ≡ nothing →
    expected ≡ SoupTerm.K Source.`unit →
    OptionalThreadImage threads slot expected

record LocalImage
  {k n m : ℕ}
  (P : Typed.Proc k)
  (logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P))
  (sigma : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m) : Set where
  field
    channelEmbedding-injective :
      ∀ {i j} →
      physicalChannel (lookup logicalChannels i) ≡
      physicalChannel (lookup logicalChannels j) →
      i ≡ j

    threadEmbedding : 𝔽 (Translation.processCount P) → Maybe (𝔽 m)
    threadEmbedding-injective :
      ∀ {i j l} →
      threadEmbedding i ≡ just l →
      threadEmbedding j ≡ just l →
      i ≡ j

    live-channel :
      (i : 𝔽 (Translation.channelCount P)) →
      lookup (Soup.channels C)
        (physicalChannel (lookup logicalChannels i)) ≡
      lookup (proj₁ (flattenOriented P logicalChannels sigma)) i

    live-thread :
      (j : 𝔽 (Translation.processCount P)) →
      OptionalThreadImage {n = n} (Soup.threads C) (threadEmbedding j)
        (lookup (proj₂ (flattenOriented P logicalChannels sigma)) j)

    garbage-channel :
      (i : 𝔽 n) →
      LocalOutside
        (physicalChannel ∘ lookup logicalChannels) i →
      ¬ ambientChannel i →
      lookup (Soup.channels C) i ≡ (false , [] , [])

    garbage-thread :
      (j : 𝔽 m) →
      OptionalOutside threadEmbedding j →
      ¬ ambientThread j →
      lookup (Soup.threads C) j ≡ SoupTerm.K Source.`unit

open LocalImage public
