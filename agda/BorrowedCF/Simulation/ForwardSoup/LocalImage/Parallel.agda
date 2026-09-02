module BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (_∪ᵖ_; ownedChannels; ownedThreads)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
  using ( take-++ˡ; drop-++ˡ; lookup-take; lookup-drop
        ; retarget-thread; flatten-par-channels; flatten-par-threads
        )

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Case analysis on an index into a concatenation.

split-elim :
  (p : ℕ) {q : ℕ} (Motive : 𝔽 (p + q) → Set) →
  ((x : 𝔽 p) → Motive (x ↑ˡ q)) →
  ((y : 𝔽 q) → Motive (p ↑ʳ y)) →
  (i : 𝔽 (p + q)) → Motive i
split-elim zero    Motive onLeft onRight i       = onRight i
split-elim (suc p) Motive onLeft onRight zero    = onLeft zero
split-elim (suc p) Motive onLeft onRight (suc i) =
  split-elim p (Motive ∘ suc) (onLeft ∘ suc) onRight i

-- Transporting a thread image along an equality of slots.

slot-cong :
  {threads : Vec (Soup.Thread n) m} {slot slot′ : Maybe (𝔽 m)}
  {expected : Soup.Thread n} →
  slot ≡ slot′ →
  OptionalThreadImage {n = n} threads slot expected →
  OptionalThreadImage {n = n} threads slot′ expected
slot-cong refl image = image

------------------------------------------------------------------------
-- Splitting the image of a parallel composition.

module _
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannels :
    Vec (OrientedChannel n) (Translation.channelCount (P Typed.∥ Q))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m}
  (image :
    LocalImage (P Typed.∥ Q) logicalChannels sigma
      ambientChannel ambientThread C)
  where

  private
    takeLookup :
      (i : 𝔽 (Translation.channelCount P)) →
      lookup (V.take (Translation.channelCount P) logicalChannels) i ≡
      lookup logicalChannels (i ↑ˡ Translation.channelCount Q)
    takeLookup = lookup-take (Translation.channelCount P) logicalChannels

    dropLookup :
      (i : 𝔽 (Translation.channelCount Q)) →
      lookup (V.drop (Translation.channelCount P) logicalChannels) i ≡
      lookup logicalChannels (Translation.channelCount P ↑ʳ i)
    dropLookup = lookup-drop (Translation.channelCount P) logicalChannels

    channelsP : Vec Soup.Channel (Translation.channelCount P)
    channelsP =
      proj₁ (flattenOriented P
              (V.take (Translation.channelCount P) logicalChannels) sigma)

    channelsQ : Vec Soup.Channel (Translation.channelCount Q)
    channelsQ =
      proj₁ (flattenOriented Q
              (V.drop (Translation.channelCount P) logicalChannels) sigma)

    threadsP : Vec (Soup.Thread n) (Translation.processCount P)
    threadsP =
      proj₂ (flattenOriented P
              (V.take (Translation.channelCount P) logicalChannels) sigma)

    threadsQ : Vec (Soup.Thread n) (Translation.processCount Q)
    threadsQ =
      proj₂ (flattenOriented Q
              (V.drop (Translation.channelCount P) logicalChannels) sigma)

    channelsSplit :
      proj₁ (flattenOriented (P Typed.∥ Q) logicalChannels sigma) ≡
      channelsP V.++ channelsQ
    channelsSplit = flatten-par-channels P Q logicalChannels sigma

    threadsSplit :
      proj₂ (flattenOriented (P Typed.∥ Q) logicalChannels sigma) ≡
      threadsP V.++ threadsQ
    threadsSplit = flatten-par-threads P Q logicalChannels sigma

    flatChannelLeft :
      (i : 𝔽 (Translation.channelCount P)) →
      lookup (proj₁ (flattenOriented (P Typed.∥ Q) logicalChannels sigma))
        (i ↑ˡ Translation.channelCount Q) ≡
      lookup channelsP i
    flatChannelLeft i =
      cong (λ channels → lookup channels (i ↑ˡ Translation.channelCount Q))
        channelsSplit ■
      V.lookup-++ˡ channelsP channelsQ i

    flatChannelRight :
      (i : 𝔽 (Translation.channelCount Q)) →
      lookup (proj₁ (flattenOriented (P Typed.∥ Q) logicalChannels sigma))
        (Translation.channelCount P ↑ʳ i) ≡
      lookup channelsQ i
    flatChannelRight i =
      cong (λ channels → lookup channels (Translation.channelCount P ↑ʳ i))
        channelsSplit ■
      V.lookup-++ʳ channelsP channelsQ i

    flatThreadLeft :
      (j : 𝔽 (Translation.processCount P)) →
      lookup (proj₂ (flattenOriented (P Typed.∥ Q) logicalChannels sigma))
        (j ↑ˡ Translation.processCount Q) ≡
      lookup threadsP j
    flatThreadLeft j =
      cong (λ threads → lookup threads (j ↑ˡ Translation.processCount Q))
        threadsSplit ■
      V.lookup-++ˡ threadsP threadsQ j

    flatThreadRight :
      (j : 𝔽 (Translation.processCount Q)) →
      lookup (proj₂ (flattenOriented (P Typed.∥ Q) logicalChannels sigma))
        (Translation.processCount P ↑ʳ j) ≡
      lookup threadsQ j
    flatThreadRight j =
      cong (λ threads → lookup threads (Translation.processCount P ↑ʳ j))
        threadsSplit ■
      V.lookup-++ʳ threadsP threadsQ j

    -- A channel that is outside the left half and neither ambient nor owned
    -- by the right half is outside the whole composition.
    outsideChannelLeft :
      (i : 𝔽 n) →
      LocalOutside
        (physicalChannel ∘
          lookup (V.take (Translation.channelCount P) logicalChannels)) i →
      ¬ (ambientChannel ∪ᵖ
          ownedChannels
            (V.drop (Translation.channelCount P) logicalChannels)) i →
      LocalOutside (physicalChannel ∘ lookup logicalChannels) i
    outsideChannelLeft i outside notAmbient =
      split-elim (Translation.channelCount P)
        (λ j → physicalChannel (lookup logicalChannels j) ≢ i)
        (λ x equal →
          outside x (cong physicalChannel (takeLookup x) ■ equal))
        (λ y equal →
          notAmbient
            (inj₂ (y , (cong physicalChannel (dropLookup y) ■ equal))))

    outsideChannelRight :
      (i : 𝔽 n) →
      LocalOutside
        (physicalChannel ∘
          lookup (V.drop (Translation.channelCount P) logicalChannels)) i →
      ¬ (ambientChannel ∪ᵖ
          ownedChannels
            (V.take (Translation.channelCount P) logicalChannels)) i →
      LocalOutside (physicalChannel ∘ lookup logicalChannels) i
    outsideChannelRight i outside notAmbient =
      split-elim (Translation.channelCount P)
        (λ j → physicalChannel (lookup logicalChannels j) ≢ i)
        (λ x equal →
          notAmbient
            (inj₂ (x , (cong physicalChannel (takeLookup x) ■ equal))))
        (λ y equal →
          outside y (cong physicalChannel (dropLookup y) ■ equal))

    outsideThreadLeft :
      (l : 𝔽 m) →
      OptionalOutside
        (threadEmbedding image ∘ (_↑ˡ Translation.processCount Q)) l →
      ¬ (ambientThread ∪ᵖ
          ownedThreads
            (threadEmbedding image ∘
              (Translation.processCount P ↑ʳ_))) l →
      OptionalOutside (threadEmbedding image) l
    outsideThreadLeft l outside notAmbient =
      split-elim (Translation.processCount P)
        (λ j → threadEmbedding image j ≢ just l)
        (λ x → outside x)
        (λ y equal → notAmbient (inj₂ (y , equal)))

    outsideThreadRight :
      (l : 𝔽 m) →
      OptionalOutside
        (threadEmbedding image ∘ (Translation.processCount P ↑ʳ_)) l →
      ¬ (ambientThread ∪ᵖ
          ownedThreads
            (threadEmbedding image ∘
              (_↑ˡ Translation.processCount Q))) l →
      OptionalOutside (threadEmbedding image) l
    outsideThreadRight l outside notAmbient =
      split-elim (Translation.processCount P)
        (λ j → threadEmbedding image j ≢ just l)
        (λ x equal → notAmbient (inj₂ (x , equal)))
        (λ y → outside y)

  par-split-left :
    LocalImage P (V.take (Translation.channelCount P) logicalChannels) sigma
      (ambientChannel ∪ᵖ
        ownedChannels (V.drop (Translation.channelCount P) logicalChannels))
      (ambientThread ∪ᵖ
        ownedThreads
          (threadEmbedding image ∘ (Translation.processCount P ↑ʳ_)))
      C
  par-split-left = record
    { channelEmbedding-injective = λ {i} {j} equal →
        Fin.↑ˡ-injective (Translation.channelCount Q) i j
          (channelEmbedding-injective image
            (sym (cong physicalChannel (takeLookup i)) ■ equal ■
             cong physicalChannel (takeLookup j)))
    ; threadEmbedding =
        threadEmbedding image ∘ (_↑ˡ Translation.processCount Q)
    ; threadEmbedding-injective = λ {i} {j} equalᵢ equalⱼ →
        Fin.↑ˡ-injective (Translation.processCount Q) i j
          (threadEmbedding-injective image equalᵢ equalⱼ)
    ; channel-not-ambient = λ i → λ where
        (inj₁ ambient) →
          channel-not-ambient image (i ↑ˡ Translation.channelCount Q)
            (subst ambientChannel
              (cong physicalChannel (takeLookup i)) ambient)
        (inj₂ (j , owned)) →
          ↑ˡ≢↑ʳ (sym
            (channelEmbedding-injective image
              (sym (cong physicalChannel (dropLookup j)) ■ owned ■
               cong physicalChannel (takeLookup i))))
    ; thread-not-ambient = λ {i} {l} embedded → λ where
        (inj₁ ambient) → thread-not-ambient image embedded ambient
        (inj₂ (j , owned)) →
          ↑ˡ≢↑ʳ (threadEmbedding-injective image embedded owned)
    ; live-channel = λ i →
        cong (λ channel → lookup (Soup.channels C) (physicalChannel channel))
          (takeLookup i) ■
        live-channel image (i ↑ˡ Translation.channelCount Q) ■
        flatChannelLeft i
    ; live-thread = λ j →
        retarget-thread {threads = Soup.threads C} (flatThreadLeft j)
          (live-thread image (j ↑ˡ Translation.processCount Q))
    ; garbage-channel = λ i outside notAmbient →
        garbage-channel image i
          (outsideChannelLeft i outside notAmbient)
          (notAmbient ∘ inj₁)
    ; garbage-thread = λ l outside notAmbient →
        garbage-thread image l
          (outsideThreadLeft l outside notAmbient)
          (notAmbient ∘ inj₁)
    }

  par-split-right :
    LocalImage Q (V.drop (Translation.channelCount P) logicalChannels) sigma
      (ambientChannel ∪ᵖ
        ownedChannels (V.take (Translation.channelCount P) logicalChannels))
      (ambientThread ∪ᵖ
        ownedThreads
          (threadEmbedding image ∘ (_↑ˡ Translation.processCount Q)))
      C
  par-split-right = record
    { channelEmbedding-injective = λ {i} {j} equal →
        Fin.↑ʳ-injective (Translation.channelCount P) i j
          (channelEmbedding-injective image
            (sym (cong physicalChannel (dropLookup i)) ■ equal ■
             cong physicalChannel (dropLookup j)))
    ; threadEmbedding =
        threadEmbedding image ∘ (Translation.processCount P ↑ʳ_)
    ; threadEmbedding-injective = λ {i} {j} equalᵢ equalⱼ →
        Fin.↑ʳ-injective (Translation.processCount P) i j
          (threadEmbedding-injective image equalᵢ equalⱼ)
    ; channel-not-ambient = λ i → λ where
        (inj₁ ambient) →
          channel-not-ambient image (Translation.channelCount P ↑ʳ i)
            (subst ambientChannel
              (cong physicalChannel (dropLookup i)) ambient)
        (inj₂ (j , owned)) →
          ↑ˡ≢↑ʳ
            (channelEmbedding-injective image
              (sym (cong physicalChannel (takeLookup j)) ■ owned ■
               cong physicalChannel (dropLookup i)))
    ; thread-not-ambient = λ {i} {l} embedded → λ where
        (inj₁ ambient) → thread-not-ambient image embedded ambient
        (inj₂ (j , owned)) →
          ↑ˡ≢↑ʳ (threadEmbedding-injective image owned embedded)
    ; live-channel = λ i →
        cong (λ channel → lookup (Soup.channels C) (physicalChannel channel))
          (dropLookup i) ■
        live-channel image (Translation.channelCount P ↑ʳ i) ■
        flatChannelRight i
    ; live-thread = λ j →
        retarget-thread {threads = Soup.threads C} (flatThreadRight j)
          (live-thread image (Translation.processCount P ↑ʳ j))
    ; garbage-channel = λ i outside notAmbient →
        garbage-channel image i
          (outsideChannelRight i outside notAmbient)
          (notAmbient ∘ inj₁)
    ; garbage-thread = λ l outside notAmbient →
        garbage-thread image l
          (outsideThreadRight l outside notAmbient)
          (notAmbient ∘ inj₁)
    }

------------------------------------------------------------------------
-- Joining two images into the image of a parallel composition.

module _
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannelsP : Vec (OrientedChannel n) (Translation.channelCount P)}
  {logicalChannelsQ : Vec (OrientedChannel n) (Translation.channelCount Q)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel ambientChannel₁ ambientChannel₂ : 𝔽 n → Set}
  {ambientThread ambientThread₁ ambientThread₂ : 𝔽 m → Set}
  {C : Soup.Config n m}
  (imageP :
    LocalImage P logicalChannelsP sigma ambientChannel₁ ambientThread₁ C)
  (imageQ :
    LocalImage Q logicalChannelsQ sigma ambientChannel₂ ambientThread₂ C)
  (right-channels-ambient :
    (j : 𝔽 (Translation.channelCount Q)) →
    ambientChannel₁ (physicalChannel (lookup logicalChannelsQ j)))
  (right-threads-ambient :
    ∀ {j l} → threadEmbedding imageQ j ≡ just l → ambientThread₁ l)
  (ambient-channel-left : (i : 𝔽 n) → ambientChannel i → ambientChannel₁ i)
  (ambient-channel-right : (i : 𝔽 n) → ambientChannel i → ambientChannel₂ i)
  (ambient-thread-left : (l : 𝔽 m) → ambientThread l → ambientThread₁ l)
  (ambient-thread-right : (l : 𝔽 m) → ambientThread l → ambientThread₂ l)
  (ambient-channel-split :
    (i : 𝔽 n) →
    ambientChannel₁ i → ambientChannel i ⊎ ownedChannels logicalChannelsQ i)
  (ambient-thread-split :
    (l : 𝔽 m) →
    ambientThread₁ l →
    ambientThread l ⊎ ownedThreads (threadEmbedding imageQ) l)
  where

  private
    joinedChannels :
      Vec (OrientedChannel n) (Translation.channelCount (P Typed.∥ Q))
    joinedChannels = logicalChannelsP V.++ logicalChannelsQ

    joinEmbedding :
      𝔽 (Translation.processCount (P Typed.∥ Q)) → Maybe (𝔽 m)
    joinEmbedding =
      [ threadEmbedding imageP , threadEmbedding imageQ ]′ ∘
      Fin.splitAt (Translation.processCount P)

    joinEmbedding-left :
      (x : 𝔽 (Translation.processCount P)) →
      joinEmbedding (x ↑ˡ Translation.processCount Q) ≡
      threadEmbedding imageP x
    joinEmbedding-left x =
      cong [ threadEmbedding imageP , threadEmbedding imageQ ]′
        (Fin.splitAt-↑ˡ (Translation.processCount P) x
          (Translation.processCount Q))

    joinEmbedding-right :
      (y : 𝔽 (Translation.processCount Q)) →
      joinEmbedding (Translation.processCount P ↑ʳ y) ≡
      threadEmbedding imageQ y
    joinEmbedding-right y =
      cong [ threadEmbedding imageP , threadEmbedding imageQ ]′
        (Fin.splitAt-↑ʳ (Translation.processCount P)
          (Translation.processCount Q) y)

    channelsP : Vec Soup.Channel (Translation.channelCount P)
    channelsP = proj₁ (flattenOriented P logicalChannelsP sigma)

    channelsQ : Vec Soup.Channel (Translation.channelCount Q)
    channelsQ = proj₁ (flattenOriented Q logicalChannelsQ sigma)

    threadsP : Vec (Soup.Thread n) (Translation.processCount P)
    threadsP = proj₂ (flattenOriented P logicalChannelsP sigma)

    threadsQ : Vec (Soup.Thread n) (Translation.processCount Q)
    threadsQ = proj₂ (flattenOriented Q logicalChannelsQ sigma)

    channelsJoin :
      proj₁ (flattenOriented (P Typed.∥ Q) joinedChannels sigma) ≡
      channelsP V.++ channelsQ
    channelsJoin =
      flatten-par-channels P Q joinedChannels sigma ■
      cong₂ V._++_
        (cong (λ channels → proj₁ (flattenOriented P channels sigma))
          (take-++ˡ logicalChannelsP logicalChannelsQ))
        (cong (λ channels → proj₁ (flattenOriented Q channels sigma))
          (drop-++ˡ logicalChannelsP logicalChannelsQ))

    threadsJoin :
      proj₂ (flattenOriented (P Typed.∥ Q) joinedChannels sigma) ≡
      threadsP V.++ threadsQ
    threadsJoin =
      flatten-par-threads P Q joinedChannels sigma ■
      cong₂ V._++_
        (cong (λ channels → proj₂ (flattenOriented P channels sigma))
          (take-++ˡ logicalChannelsP logicalChannelsQ))
        (cong (λ channels → proj₂ (flattenOriented Q channels sigma))
          (drop-++ˡ logicalChannelsP logicalChannelsQ))

    joinChannelLeft :
      (x : 𝔽 (Translation.channelCount P)) →
      physicalChannel
        (lookup joinedChannels (x ↑ˡ Translation.channelCount Q)) ≡
      physicalChannel (lookup logicalChannelsP x)
    joinChannelLeft x =
      cong physicalChannel
        (V.lookup-++ˡ logicalChannelsP logicalChannelsQ x)

    joinChannelRight :
      (y : 𝔽 (Translation.channelCount Q)) →
      physicalChannel
        (lookup joinedChannels (Translation.channelCount P ↑ʳ y)) ≡
      physicalChannel (lookup logicalChannelsQ y)
    joinChannelRight y =
      cong physicalChannel
        (V.lookup-++ʳ logicalChannelsP logicalChannelsQ y)

    joinFlatChannelLeft :
      (x : 𝔽 (Translation.channelCount P)) →
      lookup channelsP x ≡
      lookup (proj₁ (flattenOriented (P Typed.∥ Q) joinedChannels sigma))
        (x ↑ˡ Translation.channelCount Q)
    joinFlatChannelLeft x =
      sym (V.lookup-++ˡ channelsP channelsQ x) ■
      cong (λ channels → lookup channels (x ↑ˡ Translation.channelCount Q))
        (sym channelsJoin)

    joinFlatChannelRight :
      (y : 𝔽 (Translation.channelCount Q)) →
      lookup channelsQ y ≡
      lookup (proj₁ (flattenOriented (P Typed.∥ Q) joinedChannels sigma))
        (Translation.channelCount P ↑ʳ y)
    joinFlatChannelRight y =
      sym (V.lookup-++ʳ channelsP channelsQ y) ■
      cong (λ channels →
             lookup channels (Translation.channelCount P ↑ʳ y))
        (sym channelsJoin)

    joinFlatThreadLeft :
      (x : 𝔽 (Translation.processCount P)) →
      lookup threadsP x ≡
      lookup (proj₂ (flattenOriented (P Typed.∥ Q) joinedChannels sigma))
        (x ↑ˡ Translation.processCount Q)
    joinFlatThreadLeft x =
      sym (V.lookup-++ˡ threadsP threadsQ x) ■
      cong (λ threads → lookup threads (x ↑ˡ Translation.processCount Q))
        (sym threadsJoin)

    joinFlatThreadRight :
      (y : 𝔽 (Translation.processCount Q)) →
      lookup threadsQ y ≡
      lookup (proj₂ (flattenOriented (P Typed.∥ Q) joinedChannels sigma))
        (Translation.processCount P ↑ʳ y)
    joinFlatThreadRight y =
      sym (V.lookup-++ʳ threadsP threadsQ y) ■
      cong (λ threads →
             lookup threads (Translation.processCount P ↑ʳ y))
        (sym threadsJoin)

    joinChannelInjective :
      (i j : 𝔽 (Translation.channelCount (P Typed.∥ Q))) →
      physicalChannel (lookup joinedChannels i) ≡
      physicalChannel (lookup joinedChannels j) →
      i ≡ j
    joinChannelInjective =
      split-elim (Translation.channelCount P)
        (λ i →
          (j : 𝔽 (Translation.channelCount (P Typed.∥ Q))) →
          physicalChannel (lookup joinedChannels i) ≡
          physicalChannel (lookup joinedChannels j) →
          i ≡ j)
        leftCase rightCase
      where
      leftCase :
        (x : 𝔽 (Translation.channelCount P))
        (j : 𝔽 (Translation.channelCount (P Typed.∥ Q))) →
        physicalChannel
          (lookup joinedChannels (x ↑ˡ Translation.channelCount Q)) ≡
        physicalChannel (lookup joinedChannels j) →
        x ↑ˡ Translation.channelCount Q ≡ j
      leftCase x =
        split-elim (Translation.channelCount P)
          (λ j →
            physicalChannel
              (lookup joinedChannels (x ↑ˡ Translation.channelCount Q)) ≡
            physicalChannel (lookup joinedChannels j) →
            x ↑ˡ Translation.channelCount Q ≡ j)
          (λ x′ equal →
            cong (_↑ˡ Translation.channelCount Q)
              (channelEmbedding-injective imageP
                (sym (joinChannelLeft x) ■ equal ■ joinChannelLeft x′)))
          (λ y equal →
            ⊥-elim
              (channel-not-ambient imageP x
                (subst ambientChannel₁
                  (sym (sym (joinChannelLeft x) ■ equal ■
                        joinChannelRight y))
                  (right-channels-ambient y))))

      rightCase :
        (y : 𝔽 (Translation.channelCount Q))
        (j : 𝔽 (Translation.channelCount (P Typed.∥ Q))) →
        physicalChannel
          (lookup joinedChannels (Translation.channelCount P ↑ʳ y)) ≡
        physicalChannel (lookup joinedChannels j) →
        Translation.channelCount P ↑ʳ y ≡ j
      rightCase y =
        split-elim (Translation.channelCount P)
          (λ j →
            physicalChannel
              (lookup joinedChannels (Translation.channelCount P ↑ʳ y)) ≡
            physicalChannel (lookup joinedChannels j) →
            Translation.channelCount P ↑ʳ y ≡ j)
          (λ x equal →
            ⊥-elim
              (channel-not-ambient imageP x
                (subst ambientChannel₁
                  (sym (joinChannelRight y) ■ equal ■ joinChannelLeft x)
                  (right-channels-ambient y))))
          (λ y′ equal →
            cong (Translation.channelCount P ↑ʳ_)
              (channelEmbedding-injective imageQ
                (sym (joinChannelRight y) ■ equal ■ joinChannelRight y′)))

    joinThreadInjective :
      (i j : 𝔽 (Translation.processCount (P Typed.∥ Q))) (l : 𝔽 m) →
      joinEmbedding i ≡ just l → joinEmbedding j ≡ just l → i ≡ j
    joinThreadInjective =
      split-elim (Translation.processCount P)
        (λ i →
          (j : 𝔽 (Translation.processCount (P Typed.∥ Q))) (l : 𝔽 m) →
          joinEmbedding i ≡ just l → joinEmbedding j ≡ just l → i ≡ j)
        leftCase rightCase
      where
      leftCase :
        (x : 𝔽 (Translation.processCount P))
        (j : 𝔽 (Translation.processCount (P Typed.∥ Q))) (l : 𝔽 m) →
        joinEmbedding (x ↑ˡ Translation.processCount Q) ≡ just l →
        joinEmbedding j ≡ just l →
        x ↑ˡ Translation.processCount Q ≡ j
      leftCase x =
        split-elim (Translation.processCount P)
          (λ j →
            (l : 𝔽 m) →
            joinEmbedding (x ↑ˡ Translation.processCount Q) ≡ just l →
            joinEmbedding j ≡ just l →
            x ↑ˡ Translation.processCount Q ≡ j)
          (λ x′ l equalᵢ equalⱼ →
            cong (_↑ˡ Translation.processCount Q)
              (threadEmbedding-injective imageP
                (sym (joinEmbedding-left x) ■ equalᵢ)
                (sym (joinEmbedding-left x′) ■ equalⱼ)))
          (λ y l equalᵢ equalⱼ →
            ⊥-elim
              (thread-not-ambient imageP
                (sym (joinEmbedding-left x) ■ equalᵢ)
                (right-threads-ambient
                  (sym (joinEmbedding-right y) ■ equalⱼ))))

      rightCase :
        (y : 𝔽 (Translation.processCount Q))
        (j : 𝔽 (Translation.processCount (P Typed.∥ Q))) (l : 𝔽 m) →
        joinEmbedding (Translation.processCount P ↑ʳ y) ≡ just l →
        joinEmbedding j ≡ just l →
        Translation.processCount P ↑ʳ y ≡ j
      rightCase y =
        split-elim (Translation.processCount P)
          (λ j →
            (l : 𝔽 m) →
            joinEmbedding (Translation.processCount P ↑ʳ y) ≡ just l →
            joinEmbedding j ≡ just l →
            Translation.processCount P ↑ʳ y ≡ j)
          (λ x l equalᵢ equalⱼ →
            ⊥-elim
              (thread-not-ambient imageP
                (sym (joinEmbedding-left x) ■ equalⱼ)
                (right-threads-ambient
                  (sym (joinEmbedding-right y) ■ equalᵢ))))
          (λ y′ l equalᵢ equalⱼ →
            cong (Translation.processCount P ↑ʳ_)
              (threadEmbedding-injective imageQ
                (sym (joinEmbedding-right y) ■ equalᵢ)
                (sym (joinEmbedding-right y′) ■ equalⱼ)))

    joinChannelNotAmbient :
      (i : 𝔽 (Translation.channelCount (P Typed.∥ Q))) →
      ¬ ambientChannel (physicalChannel (lookup joinedChannels i))
    joinChannelNotAmbient =
      split-elim (Translation.channelCount P)
        (λ i → ¬ ambientChannel (physicalChannel (lookup joinedChannels i)))
        (λ x ambient →
          channel-not-ambient imageP x
            (subst ambientChannel₁ (joinChannelLeft x)
              (ambient-channel-left _ ambient)))
        (λ y ambient →
          channel-not-ambient imageQ y
            (subst ambientChannel₂ (joinChannelRight y)
              (ambient-channel-right _ ambient)))

    joinThreadNotAmbient :
      (i : 𝔽 (Translation.processCount (P Typed.∥ Q))) {l : 𝔽 m} →
      joinEmbedding i ≡ just l → ¬ ambientThread l
    joinThreadNotAmbient =
      split-elim (Translation.processCount P)
        (λ i → {l : 𝔽 m} → joinEmbedding i ≡ just l → ¬ ambientThread l)
        (λ x embedded ambient →
          thread-not-ambient imageP
            (sym (joinEmbedding-left x) ■ embedded)
            (ambient-thread-left _ ambient))
        (λ y embedded ambient →
          thread-not-ambient imageQ
            (sym (joinEmbedding-right y) ■ embedded)
            (ambient-thread-right _ ambient))

    joinLiveChannel :
      (i : 𝔽 (Translation.channelCount (P Typed.∥ Q))) →
      lookup (Soup.channels C)
        (physicalChannel (lookup joinedChannels i)) ≡
      lookup (proj₁ (flattenOriented (P Typed.∥ Q) joinedChannels sigma)) i
    joinLiveChannel =
      split-elim (Translation.channelCount P)
        (λ i →
          lookup (Soup.channels C)
            (physicalChannel (lookup joinedChannels i)) ≡
          lookup
            (proj₁ (flattenOriented (P Typed.∥ Q) joinedChannels sigma)) i)
        (λ x →
          cong (lookup (Soup.channels C)) (joinChannelLeft x) ■
          live-channel imageP x ■
          joinFlatChannelLeft x)
        (λ y →
          cong (lookup (Soup.channels C)) (joinChannelRight y) ■
          live-channel imageQ y ■
          joinFlatChannelRight y)

    joinLiveThread :
      (j : 𝔽 (Translation.processCount (P Typed.∥ Q))) →
      OptionalThreadImage {n = n} (Soup.threads C) (joinEmbedding j)
        (lookup
          (proj₂ (flattenOriented (P Typed.∥ Q) joinedChannels sigma)) j)
    joinLiveThread =
      split-elim (Translation.processCount P)
        (λ j →
          OptionalThreadImage {n = n} (Soup.threads C) (joinEmbedding j)
            (lookup
              (proj₂ (flattenOriented (P Typed.∥ Q) joinedChannels sigma)) j))
        (λ x →
          slot-cong (sym (joinEmbedding-left x))
            (retarget-thread {threads = Soup.threads C}
              (joinFlatThreadLeft x) (live-thread imageP x)))
        (λ y →
          slot-cong (sym (joinEmbedding-right y))
            (retarget-thread {threads = Soup.threads C}
              (joinFlatThreadRight y) (live-thread imageQ y)))

    joinGarbageChannel :
      (i : 𝔽 n) →
      LocalOutside (physicalChannel ∘ lookup joinedChannels) i →
      ¬ ambientChannel i →
      lookup (Soup.channels C) i ≡ (false , [] , [])
    joinGarbageChannel i outside notAmbient =
      garbage-channel imageP i
        (λ x equal →
          outside (x ↑ˡ Translation.channelCount Q)
            (joinChannelLeft x ■ equal))
        (λ ambient →
          [ notAmbient
          , (λ where
              (y , owned) →
                outside (Translation.channelCount P ↑ʳ y)
                  (joinChannelRight y ■ owned))
          ]′ (ambient-channel-split i ambient))

    joinGarbageThread :
      (l : 𝔽 m) →
      OptionalOutside joinEmbedding l →
      ¬ ambientThread l →
      lookup (Soup.threads C) l ≡ SoupTerm.K Source.`unit
    joinGarbageThread l outside notAmbient =
      garbage-thread imageP l
        (λ x embedded →
          outside (x ↑ˡ Translation.processCount Q)
            (joinEmbedding-left x ■ embedded))
        (λ ambient →
          [ notAmbient
          , (λ where
              (y , embedded) →
                outside (Translation.processCount P ↑ʳ y)
                  (joinEmbedding-right y ■ embedded))
          ]′ (ambient-thread-split l ambient))

  par-join :
    LocalImage (P Typed.∥ Q) (logicalChannelsP V.++ logicalChannelsQ) sigma
      ambientChannel ambientThread C
  par-join = record
    { channelEmbedding-injective = λ {i} {j} → joinChannelInjective i j
    ; threadEmbedding = joinEmbedding
    ; threadEmbedding-injective = λ {i} {j} {l} equalᵢ equalⱼ →
        joinThreadInjective i j l equalᵢ equalⱼ
    ; channel-not-ambient = joinChannelNotAmbient
    ; thread-not-ambient = λ {i} → joinThreadNotAmbient i
    ; live-channel = joinLiveChannel
    ; live-thread = joinLiveThread
    ; garbage-channel = joinGarbageChannel
    ; garbage-thread = joinGarbageThread
    }
