module BorrowedCF.Simulation.ForwardSoup.LocalImage.Embedding where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (ownedChannels; ownedThreads)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.PhysicalRenaming
  using ( renameEnv; renameOriented; physicalChannel-rename
        ; flattenChannels-physical; flattenThreads-physical
        )
open import BorrowedCF.Simulation.ForwardSoup.World.Embedding
  using (AmbientEmbedding; module AmbientEmbedding)

open Nat.Variables

private variable a : ℕ

------------------------------------------------------------------------
-- Transporting the local resources of an image along an ambient
-- embedding.

embedChannels :
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {source : Soup.Config n m} {target : Soup.Config n′ m′} →
  AmbientEmbedding ambientChannel ambientThread source target →
  Vec (OrientedChannel n) a →
  Vec (OrientedChannel n′) a
embedChannels embedding =
  V.map (renameOriented (AmbientEmbedding.channelEmbedding embedding))

embedThreads :
  {P : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel₁ ambientChannel : 𝔽 n → Set}
  {ambientThread₁ ambientThread : 𝔽 m → Set}
  {source : Soup.Config n m} {target : Soup.Config n′ m′} →
  AmbientEmbedding ambientChannel₁ ambientThread₁ source target →
  LocalImage P logicalChannels sigma ambientChannel ambientThread source →
  𝔽 (Translation.processCount P) → Maybe (𝔽 m′)
embedThreads embedding image =
  mapMaybe (AmbientEmbedding.threadEmbedding embedding) ∘
  threadEmbedding image

------------------------------------------------------------------------
-- Auxiliary lemmas.

physicalChannel-embed :
  (channelRho : 𝔽 n → 𝔽 n′)
  (logicalChannels : Vec (OrientedChannel n) a)
  (i : 𝔽 a) →
  physicalChannel (lookup (V.map (renameOriented channelRho) logicalChannels) i) ≡
  channelRho (physicalChannel (lookup logicalChannels i))
physicalChannel-embed channelRho logicalChannels i =
  cong physicalChannel (lookup-map i (renameOriented channelRho) logicalChannels)
  ■ physicalChannel-rename channelRho (lookup logicalChannels i)

private
  mapMaybe-just :
    {b : ℕ} (threadRho : 𝔽 a → 𝔽 b) (slot : Maybe (𝔽 a)) {l : 𝔽 b} →
    mapMaybe threadRho slot ≡ just l →
    Σ[ source ∈ 𝔽 a ] (slot ≡ just source × threadRho source ≡ l)
  mapMaybe-just threadRho (just source) refl = source , refl , refl
  mapMaybe-just threadRho nothing ()

------------------------------------------------------------------------
-- The transport itself.  The ambient sets of the transported image are
-- the complements of the transported local resources, so both garbage
-- clauses are vacuous.

ambient-transport :
  {Q : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount Q)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel₁ ambientChannel : 𝔽 n → Set}
  {ambientThread₁ ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} {C′ : Soup.Config n′ m′}
  (embedding : AmbientEmbedding ambientChannel₁ ambientThread₁ C C′)
  (image : LocalImage Q logicalChannels sigma ambientChannel ambientThread C) →
  ((i : 𝔽 (Translation.channelCount Q)) →
    ambientChannel₁ (physicalChannel (lookup logicalChannels i))) →
  (∀ {j l} → threadEmbedding image j ≡ just l → ambientThread₁ l) →
  LocalImage Q
    (embedChannels embedding logicalChannels)
    (renameEnv (AmbientEmbedding.endpointEmbedding embedding) sigma)
    (λ i → ¬ ownedChannels (embedChannels embedding logicalChannels) i)
    (λ l → ¬ ownedThreads (embedThreads embedding image) l)
    C′
ambient-transport {Q = Q} {logicalChannels = logicalChannels} {sigma = sigma}
  {C′ = C′} embedding image channelsAmbient threadsAmbient = record
  { channelEmbedding-injective = λ {i} {j} entryEq →
      channelEmbedding-injective image
        (channelRho-injective
          (sym (physicalChannel-embed channelRho logicalChannels i)
           ■ entryEq
           ■ physicalChannel-embed channelRho logicalChannels j))
  ; threadEmbedding = embedThreads embedding image
  ; threadEmbedding-injective = λ {i} {j} {l} slotEqI slotEqJ →
      let sourceI = mapMaybe-just threadRho (threadEmbedding image i) slotEqI
          sourceJ = mapMaybe-just threadRho (threadEmbedding image j) slotEqJ
      in threadEmbedding-injective image
           (proj₁ (proj₂ sourceI))
           (proj₁ (proj₂ sourceJ)
            ■ cong just
                (threadRho-injective
                  (proj₂ (proj₂ sourceJ) ■ sym (proj₂ (proj₂ sourceI)))))
  ; channel-not-ambient = λ i notOwned → notOwned (i , refl)
  ; thread-not-ambient = λ {i} slotEq notOwned → notOwned (i , slotEq)
  ; live-channel = λ i →
      cong (lookup (Soup.channels C′))
        (physicalChannel-embed channelRho logicalChannels i)
      ■ ambient-channel-content
          (physicalChannel (lookup logicalChannels i)) (channelsAmbient i)
      ■ live-channel image i
      ■ sym (cong (λ terms → lookup terms i) flattenChannels-transported)
  ; live-thread = liveThread
  ; garbage-channel = λ i outside notOwned →
      ⊥-elim (notOwned (λ owned → outside (proj₁ owned) (proj₂ owned)))
  ; garbage-thread = λ l outside notOwned →
      ⊥-elim (notOwned (λ owned → outside (proj₁ owned) (proj₂ owned)))
  }
  where
  open AmbientEmbedding embedding
    renaming
      ( channelEmbedding to channelRho
      ; threadEmbedding to threadRho
      ; endpointEmbedding to endpointRho
      ; channelEmbedding-injective to channelRho-injective
      ; threadEmbedding-injective to threadRho-injective
      )

  targetEnv : Translation.Env _ _
  targetEnv = renameEnv endpointRho sigma

  envCoherent : (x : 𝔽 _) → targetEnv x ≡ sigma x SoupTerm.⋯ᵣ endpointRho
  envCoherent x = refl

  flattenChannels-transported :
    proj₁ (flattenOriented Q (embedChannels embedding logicalChannels) targetEnv)
    ≡ proj₁ (flattenOriented Q logicalChannels sigma)
  flattenChannels-transported =
    flattenChannels-physical Q channelRho endpointRho
      endpoint-respects-channel logicalChannels sigma targetEnv envCoherent

  flattenThreads-transported :
    proj₂ (flattenOriented Q (embedChannels embedding logicalChannels) targetEnv)
    ≡ V.map (SoupTerm._⋯ᵣ endpointRho)
        (proj₂ (flattenOriented Q logicalChannels sigma))
  flattenThreads-transported =
    flattenThreads-physical Q channelRho endpointRho
      endpoint-respects-channel logicalChannels sigma targetEnv envCoherent

  expected-transported :
    (j : 𝔽 (Translation.processCount Q)) →
    lookup
      (proj₂ (flattenOriented Q (embedChannels embedding logicalChannels)
               targetEnv))
      j
    ≡ lookup (proj₂ (flattenOriented Q logicalChannels sigma)) j
        SoupTerm.⋯ᵣ endpointRho
  expected-transported j =
    cong (λ terms → lookup terms j) flattenThreads-transported
    ■ lookup-map j (SoupTerm._⋯ᵣ endpointRho)
        (proj₂ (flattenOriented Q logicalChannels sigma))

  liveThread :
    (j : 𝔽 (Translation.processCount Q)) →
    OptionalThreadImage (Soup.threads C′) (embedThreads embedding image j)
      (lookup
        (proj₂ (flattenOriented Q (embedChannels embedding logicalChannels)
                 targetEnv))
        j)
  liveThread j with live-thread image j
  ... | present l slotEq contentEq =
    present (threadRho l)
      (cong (mapMaybe threadRho) slotEq)
      (ambient-thread-content l (threadsAmbient slotEq)
       ■ cong (SoupTerm._⋯ᵣ endpointRho) contentEq
       ■ sym (expected-transported j))
  ... | omitted slotEq expectedEq =
    omitted
      (cong (mapMaybe threadRho) slotEq)
      (expected-transported j ■ cong (SoupTerm._⋯ᵣ endpointRho) expectedEq)
