-- | Lifting reflected reductions through located process contexts.
module BorrowedCF.Simulation.BackwardSoup.Lift where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.Typed as TypedReduction
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( ProcessContext; hole; par-left; par-right; bind; plug
        ; focusChannels; focusEnv; threadInContext)

open import BorrowedCF.Simulation.ForwardSoup.Local.Step
  using (ConfigStep; embedding-mono)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel; res-split-not-ambient; res-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
  using (rotate; parallel-swap-image)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Embedding
  using ( ambient-transport; embedChannels; embedThreads
        ; physicalChannel-embed)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using ( _∪ᵖ_; singletonᵖ; ownedChannels; ownedThreads
        ; ambient-resp; env-resp; bindEnv; bindChannel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left; par-split-right; par-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.PhysicalRenaming
  using ( renameEnv; renameOriented; physicalEndpoint-rename
        ; UB-flags-ren; UB-ren-coherent-*; ++ₛ-ren-coherent)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (Separated)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.SeparationFrame
  using (separated-bind; separated-par-left; separated-par-right)
open import BorrowedCF.Simulation.ForwardSoup.World.Embedding
  using (Transport; AmbientEmbedding; module AmbientEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage)

open Nat.Variables hiding (n′; m′)
open Fin.Patterns

private
  variable
    a b : ℕ

  mapMaybe-just :
    (threadRho : 𝔽 a → 𝔽 b) (slot : Maybe (𝔽 a)) {l : 𝔽 b} →
    mapMaybe threadRho slot ≡ just l →
    Σ[ source ∈ 𝔽 a ] (slot ≡ just source × threadRho source ≡ l)
  mapMaybe-just threadRho (just source) refl = source , refl , refl
  mapMaybe-just threadRho nothing ()

------------------------------------------------------------------------
-- A typed reduction reconstructed at a located leaf remains a reduction of
-- the enclosing process.  The calculus only reduces the left parallel
-- component, so a right-context step is exposed and restored with
-- commutativity.

plug-red :
  ∀ {k n} →
  (ctx : ProcessContext k n) →
  {P P′ : Typed.Proc k} →
  P TypedReduction.─→ₚ P′ →
  plug ctx P TypedReduction.─→ₚ plug ctx P′
plug-red hole red = red
plug-red (par-left ctx Q) red =
  TypedReduction.R-Par (plug-red ctx red)
plug-red (par-right Q ctx) red =
  TypedReduction.R-Struct Typed.∥-comm
    (TypedReduction.R-Par (plug-red ctx red)) Typed.∥-comm
plug-red (bind B₁ B₂ ctx) red =
  TypedReduction.R-Bind (plug-red ctx red)

------------------------------------------------------------------------
-- Focusing an image at the hole of a process context and lifting any exact
-- focused soup step back through the same context.

record FocusedImage
  {k n c m : ℕ}
  (ctx : ProcessContext k n)
  (P : Typed.Proc k)
  (logicalChannels :
    Vec (OrientedChannel c) (Translation.channelCount (plug ctx P)))
  (sigma : Translation.Env n (2 *ℕ c))
  (ambientChannel : 𝔽 c → Set)
  (ambientThread : 𝔽 m → Set)
  (C : Soup.Config c m) : Set₁ where
  field
    focusedAmbientChannel : 𝔽 c → Set
    focusedAmbientThread : 𝔽 m → Set

    focused-image :
      LocalImage P
        (focusChannels ctx P logicalChannels)
        (focusEnv ctx P logicalChannels sigma)
        focusedAmbientChannel focusedAmbientThread C

    ascend :
      {P′ : Typed.Proc k} {c′ m′ : ℕ} {C′ : Soup.Config c′ m′} →
      ConfigStep P′
        (focusEnv ctx P logicalChannels sigma)
        focusedAmbientChannel focusedAmbientThread C C′ →
      ConfigStep (plug ctx P′) sigma ambientChannel ambientThread C C′

open FocusedImage public

focusImage :
  ∀ {k n c m : ℕ}
  (ctx : ProcessContext k n)
  (P : Typed.Proc k)
  {logicalChannels :
    Vec (OrientedChannel c) (Translation.channelCount (plug ctx P))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set}
  {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  LocalImage (plug ctx P) logicalChannels sigma
    ambientChannel ambientThread C →
  FocusedImage ctx P logicalChannels sigma ambientChannel ambientThread C
focusImage hole P image = record
  { focusedAmbientChannel = _
  ; focusedAmbientThread = _
  ; focused-image = image
  ; ascend = λ step → step
  }
focusImage {c = c} {m = m} (par-left ctx Q) P
  {logicalChannels = logicalChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread}
  image = record
  { focusedAmbientChannel = focusedAmbientChannel focused
  ; focusedAmbientThread = focusedAmbientThread focused
  ; focused-image = focused-image focused
  ; ascend = λ step → par-left-ascent (ascend focused step)
  }
  where
  leftChannelCount : ℕ
  leftChannelCount = Translation.channelCount (plug ctx P)

  leftProcessCount : ℕ
  leftProcessCount = Translation.processCount (plug ctx P)

  rightChannels : Vec (OrientedChannel c) (Translation.channelCount Q)
  rightChannels = V.drop leftChannelCount logicalChannels

  rightImage :
    LocalImage Q rightChannels sigma
      (ambientChannel ∪ᵖ
        ownedChannels (V.take leftChannelCount logicalChannels))
      (ambientThread ∪ᵖ
        ownedThreads
          (threadEmbedding image ∘ (_↑ˡ Translation.processCount Q)))
      _
  rightImage = par-split-right image

  focused =
    focusImage ctx P (par-split-left image)

  par-left-ascent :
    {P′ : Typed.Proc _} {c′ m′ : ℕ} {C′ : Soup.Config c′ m′} →
    ConfigStep (plug ctx P′) sigma
      (ambientChannel ∪ᵖ ownedChannels rightChannels)
      (ambientThread ∪ᵖ
        ownedThreads (threadEmbedding image ∘ (leftProcessCount ↑ʳ_)))
      _ C′ →
    ConfigStep (plug ctx P′ Typed.∥ Q) sigma
      ambientChannel ambientThread _ C′
  par-left-ascent st = record
    { config-step = ConfigStep.config-step st
    ; config-embedding =
        embedding-mono (λ _ → inj₁) (λ _ → inj₁) emb
    ; config-logicalChannels′ =
        ConfigStep.config-logicalChannels′ st V.++
        embedChannels emb rightChannels
    ; config-image′ =
        par-join (ConfigStep.config-image′ st) transportedRight
          right-channels-ambient right-threads-ambient
          ambient-channel-left ambient-channel-right
          ambient-thread-left ambient-thread-right
          ambient-channel-split ambient-thread-split
    }
    where
    emb = ConfigStep.config-embedding st
    channelRho = AmbientEmbedding.channelEmbedding emb
    threadRho = AmbientEmbedding.threadEmbedding emb

    transportedRight =
      ambient-transport emb rightImage
        (λ j → inj₂ (j , refl))
        (λ {j} {l} slotEq → inj₂ (j , slotEq))

    right-channels-ambient :
      (j : 𝔽 (Translation.channelCount Q)) →
      Transport channelRho
        (ambientChannel ∪ᵖ ownedChannels rightChannels)
        (physicalChannel (lookup (embedChannels emb rightChannels) j))
    right-channels-ambient j =
      physicalChannel (lookup rightChannels j)
      , inj₂ (j , refl)
      , sym (physicalChannel-embed channelRho rightChannels j)

    right-threads-ambient :
      ∀ {j l} →
      embedThreads emb rightImage j ≡ just l →
      Transport threadRho
        (ambientThread ∪ᵖ
          ownedThreads (threadEmbedding image ∘ (leftProcessCount ↑ʳ_)))
        l
    right-threads-ambient {j} slotEq
      with mapMaybe-just threadRho (threadEmbedding rightImage j) slotEq
    ... | source , sourceEq , threadEq =
      source , inj₂ (j , sourceEq) , threadEq

    ambient-channel-left :
      (i : 𝔽 _) →
      Transport channelRho ambientChannel i →
      Transport channelRho
        (ambientChannel ∪ᵖ ownedChannels rightChannels) i
    ambient-channel-left i (source , ambient , sourceEq) =
      source , inj₁ ambient , sourceEq

    ambient-channel-right :
      (i : 𝔽 _) →
      Transport channelRho ambientChannel i →
      ¬ ownedChannels (embedChannels emb rightChannels) i
    ambient-channel-right i (source , ambient , sourceEq) (j , ownedEq) =
      channel-not-ambient rightImage j
        (inj₁
          (subst ambientChannel
            (sym
              (AmbientEmbedding.channelEmbedding-injective emb
                (sym (physicalChannel-embed channelRho rightChannels j)
                 ■ ownedEq ■ sym sourceEq)))
            ambient))

    ambient-thread-left :
      (l : 𝔽 _) →
      Transport threadRho ambientThread l →
      Transport threadRho
        (ambientThread ∪ᵖ
          ownedThreads (threadEmbedding image ∘ (leftProcessCount ↑ʳ_)))
        l
    ambient-thread-left l (source , ambient , sourceEq) =
      source , inj₁ ambient , sourceEq

    ambient-thread-right :
      (l : 𝔽 _) →
      Transport threadRho ambientThread l →
      ¬ ownedThreads (embedThreads emb rightImage) l
    ambient-thread-right l (source , ambient , sourceEq) (j , ownedEq)
      with mapMaybe-just threadRho (threadEmbedding rightImage j) ownedEq
    ... | source′ , sourceEq′ , threadEq =
      thread-not-ambient rightImage sourceEq′
        (inj₁
          (subst ambientThread
            (sym
              (AmbientEmbedding.threadEmbedding-injective emb
                (threadEq ■ sym sourceEq)))
            ambient))

    ambient-channel-split :
      (i : 𝔽 _) →
      Transport channelRho
        (ambientChannel ∪ᵖ ownedChannels rightChannels) i →
      Transport channelRho ambientChannel i ⊎
        ownedChannels (embedChannels emb rightChannels) i
    ambient-channel-split i (source , inj₁ ambient , sourceEq) =
      inj₁ (source , ambient , sourceEq)
    ambient-channel-split i (source , inj₂ (j , ownedEq) , sourceEq) =
      inj₂
        ( j
        , (physicalChannel-embed channelRho rightChannels j
           ■ cong channelRho ownedEq ■ sourceEq)
        )

    ambient-thread-split :
      (l : 𝔽 _) →
      Transport threadRho
        (ambientThread ∪ᵖ
          ownedThreads (threadEmbedding image ∘ (leftProcessCount ↑ʳ_)))
        l →
      Transport threadRho ambientThread l ⊎
        ownedThreads (embedThreads emb rightImage) l
    ambient-thread-split l (source , inj₁ ambient , sourceEq) =
      inj₁ (source , ambient , sourceEq)
    ambient-thread-split l (source , inj₂ (j , ownedEq) , sourceEq) =
      inj₂ (j , (cong (mapMaybe threadRho) ownedEq ■ cong just sourceEq))
focusImage {c = c} {m = m} (par-right Q ctx) P
  {logicalChannels = logicalChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread}
  image = record
  { focusedAmbientChannel = focusedAmbientChannel focused
  ; focusedAmbientThread = focusedAmbientThread focused
  ; focused-image = focused-image focused
  ; ascend = λ step → par-right-ascent (ascend focused step)
  }
  where
  leftChannelCount : ℕ
  leftChannelCount = Translation.channelCount Q

  rightProcessCount : ℕ
  rightProcessCount = Translation.processCount (plug ctx P)

  leftChannels : Vec (OrientedChannel c) (Translation.channelCount Q)
  leftChannels = V.take leftChannelCount logicalChannels

  leftImage :
    LocalImage Q leftChannels sigma
      (ambientChannel ∪ᵖ
        ownedChannels (V.drop leftChannelCount logicalChannels))
      (ambientThread ∪ᵖ
        ownedThreads
          (threadEmbedding image ∘
            (Translation.processCount Q ↑ʳ_)))
      _
  leftImage = par-split-left image

  focused =
    focusImage ctx P (par-split-right image)

  par-right-ascent :
    {P′ : Typed.Proc _} {c′ m′ : ℕ} {C′ : Soup.Config c′ m′} →
    ConfigStep (plug ctx P′) sigma
      (ambientChannel ∪ᵖ ownedChannels leftChannels)
      (ambientThread ∪ᵖ
        ownedThreads (threadEmbedding image ∘ (_↑ˡ rightProcessCount)))
      _ C′ →
    ConfigStep (Q Typed.∥ plug ctx P′) sigma
      ambientChannel ambientThread _ C′
  par-right-ascent {P′ = P′} st = record
    { config-step = ConfigStep.config-step st
    ; config-embedding =
        embedding-mono (λ _ → inj₁) (λ _ → inj₁) emb
    ; config-logicalChannels′ =
        rotate (Translation.channelCount (plug ctx P′)) joinedChannels
    ; config-image′ = parallel-swap-image joined
    }
    where
    emb = ConfigStep.config-embedding st
    channelRho = AmbientEmbedding.channelEmbedding emb
    threadRho = AmbientEmbedding.threadEmbedding emb

    transportedLeft =
      ambient-transport emb leftImage
        (λ j → inj₂ (j , refl))
        (λ {j} {l} slotEq → inj₂ (j , slotEq))

    right-channels-ambient :
      (j : 𝔽 (Translation.channelCount Q)) →
      Transport channelRho
        (ambientChannel ∪ᵖ ownedChannels leftChannels)
        (physicalChannel (lookup (embedChannels emb leftChannels) j))
    right-channels-ambient j =
      physicalChannel (lookup leftChannels j)
      , inj₂ (j , refl)
      , sym (physicalChannel-embed channelRho leftChannels j)

    right-threads-ambient :
      ∀ {j l} →
      embedThreads emb leftImage j ≡ just l →
      Transport threadRho
        (ambientThread ∪ᵖ
          ownedThreads (threadEmbedding image ∘ (_↑ˡ rightProcessCount)))
        l
    right-threads-ambient {j} slotEq
      with mapMaybe-just threadRho (threadEmbedding leftImage j) slotEq
    ... | source , sourceEq , threadEq =
      source , inj₂ (j , sourceEq) , threadEq

    ambient-channel-left :
      (i : 𝔽 _) →
      Transport channelRho ambientChannel i →
      Transport channelRho
        (ambientChannel ∪ᵖ ownedChannels leftChannels) i
    ambient-channel-left i (source , ambient , sourceEq) =
      source , inj₁ ambient , sourceEq

    ambient-channel-right :
      (i : 𝔽 _) →
      Transport channelRho ambientChannel i →
      ¬ ownedChannels (embedChannels emb leftChannels) i
    ambient-channel-right i (source , ambient , sourceEq) (j , ownedEq) =
      channel-not-ambient leftImage j
        (inj₁
          (subst ambientChannel
            (sym
              (AmbientEmbedding.channelEmbedding-injective emb
                (sym (physicalChannel-embed channelRho leftChannels j)
                 ■ ownedEq ■ sym sourceEq)))
            ambient))

    ambient-thread-left :
      (l : 𝔽 _) →
      Transport threadRho ambientThread l →
      Transport threadRho
        (ambientThread ∪ᵖ
          ownedThreads (threadEmbedding image ∘ (_↑ˡ rightProcessCount)))
        l
    ambient-thread-left l (source , ambient , sourceEq) =
      source , inj₁ ambient , sourceEq

    ambient-thread-right :
      (l : 𝔽 _) →
      Transport threadRho ambientThread l →
      ¬ ownedThreads (embedThreads emb leftImage) l
    ambient-thread-right l (source , ambient , sourceEq) (j , ownedEq)
      with mapMaybe-just threadRho (threadEmbedding leftImage j) ownedEq
    ... | source′ , sourceEq′ , threadEq =
      thread-not-ambient leftImage sourceEq′
        (inj₁
          (subst ambientThread
            (sym
              (AmbientEmbedding.threadEmbedding-injective emb
                (threadEq ■ sym sourceEq)))
            ambient))

    ambient-channel-split :
      (i : 𝔽 _) →
      Transport channelRho
        (ambientChannel ∪ᵖ ownedChannels leftChannels) i →
      Transport channelRho ambientChannel i ⊎
        ownedChannels (embedChannels emb leftChannels) i
    ambient-channel-split i (source , inj₁ ambient , sourceEq) =
      inj₁ (source , ambient , sourceEq)
    ambient-channel-split i (source , inj₂ (j , ownedEq) , sourceEq) =
      inj₂
        ( j
        , (physicalChannel-embed channelRho leftChannels j
           ■ cong channelRho ownedEq ■ sourceEq)
        )

    ambient-thread-split :
      (l : 𝔽 _) →
      Transport threadRho
        (ambientThread ∪ᵖ
          ownedThreads (threadEmbedding image ∘ (_↑ˡ rightProcessCount)))
        l →
      Transport threadRho ambientThread l ⊎
        ownedThreads (embedThreads emb leftImage) l
    ambient-thread-split l (source , inj₁ ambient , sourceEq) =
      inj₁ (source , ambient , sourceEq)
    ambient-thread-split l (source , inj₂ (j , ownedEq) , sourceEq) =
      inj₂ (j , (cong (mapMaybe threadRho) ownedEq ■ cong just sourceEq))

    joinedChannels =
      ConfigStep.config-logicalChannels′ st V.++
      embedChannels emb leftChannels

    joined =
      par-join (ConfigStep.config-image′ st) transportedLeft
        right-channels-ambient right-threads-ambient
        ambient-channel-left ambient-channel-right
        ambient-thread-left ambient-thread-right
        ambient-channel-split ambient-thread-split
focusImage {c = c} {m = m} (bind B₁ B₂ ctx) P
  {logicalChannels = channel ∷ logicalChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread}
  image = record
  { focusedAmbientChannel = focusedAmbientChannel focused
  ; focusedAmbientThread = focusedAmbientThread focused
  ; focused-image = focused-image focused
  ; ascend = λ step → bind-ascent (ascend focused step)
  }
  where
  bodyImage = res-split-image image
  channelEq₀ = res-split-channel image
  notAmbient₀ = res-split-not-ambient image

  focused =
    focusImage ctx P bodyImage

  bind-ascent :
    {P′ : Typed.Proc _} {c′ m′ : ℕ} {C′ : Soup.Config c′ m′} →
    ConfigStep (plug ctx P′) (bindEnv B₁ B₂ channel sigma)
      (ambientChannel ∪ᵖ singletonᵖ (physicalChannel channel))
      ambientThread _ C′ →
    ConfigStep (Typed.ν B₁ B₂ (plug ctx P′)) sigma
      ambientChannel ambientThread _ C′
  bind-ascent {C′ = C′} st = record
    { config-step = ConfigStep.config-step st
    ; config-embedding =
        embedding-mono (λ _ → inj₁) (λ _ ambient → ambient) emb
    ; config-logicalChannels′ =
        channel′ ∷ ConfigStep.config-logicalChannels′ st
    ; config-image′ =
        res-join bodyImage₂ channelContent notAmbient
    }
    where
    emb = ConfigStep.config-embedding st
    channelRho = AmbientEmbedding.channelEmbedding emb
    endpointRho = AmbientEmbedding.endpointEmbedding emb

    channel′ : OrientedChannel _
    channel′ = renameOriented channelRho channel

    endpointEq :
      (side : 𝔽 2) →
      physicalEndpoint channel′ side ≡
      endpointRho (physicalEndpoint channel side)
    endpointEq =
      physicalEndpoint-rename channelRho endpointRho
        (AmbientEmbedding.endpoint-respects-channel emb) channel

    binderCoherent :
      (B : Typed.BindGroup) (side : 𝔽 2) (y : 𝔽 (sum B)) →
      proj₁ (Translation.UB[ B ] (physicalEndpoint channel′ side)
              (SoupTerm.* , physicalEndpoint channel′ side , SoupTerm.*)) y ≡
      proj₁ (Translation.UB[ B ] (physicalEndpoint channel side)
              (SoupTerm.* , physicalEndpoint channel side , SoupTerm.*)) y
        SoupTerm.⋯ᵣ endpointRho
    binderCoherent B side y =
      cong
        (λ endpoint →
          proj₁ (Translation.UB[ B ] endpoint
                  (SoupTerm.* , endpoint , SoupTerm.*)) y)
        (endpointEq side)
      ■ UB-ren-coherent-* B endpointRho
          (physicalEndpoint channel side) (physicalEndpoint channel side) y

    envEq :
      (x : 𝔽 (sum B₁ + sum B₂ + _)) →
      renameEnv endpointRho (bindEnv B₁ B₂ channel sigma) x ≡
      bindEnv B₁ B₂ channel′ (renameEnv endpointRho sigma) x
    envEq x =
      sym
        (++ₛ-ren-coherent endpointRho
          (++ₛ-ren-coherent endpointRho
            (binderCoherent B₁ 0F) (binderCoherent B₂ 1F))
          (λ _ → refl) x)

    bodyImage₁ =
      env-resp envEq (ConfigStep.config-image′ st)

    toChannel :
      (i : 𝔽 _) →
      Transport channelRho
        (ambientChannel ∪ᵖ singletonᵖ (physicalChannel channel)) i →
      (Transport channelRho ambientChannel ∪ᵖ
        singletonᵖ (physicalChannel channel′)) i
    toChannel i (source , inj₁ ambient , sourceEq) =
      inj₁ (source , ambient , sourceEq)
    toChannel i (source , inj₂ headEq , sourceEq) =
      inj₂ (cong channelRho headEq ■ sourceEq)

    fromChannel :
      (i : 𝔽 _) →
      (Transport channelRho ambientChannel ∪ᵖ
        singletonᵖ (physicalChannel channel′)) i →
      Transport channelRho
        (ambientChannel ∪ᵖ singletonᵖ (physicalChannel channel)) i
    fromChannel i (inj₁ (source , ambient , sourceEq)) =
      source , inj₁ ambient , sourceEq
    fromChannel i (inj₂ headEq) =
      physicalChannel channel , inj₂ refl , headEq

    bodyImage₂ =
      ambient-resp toChannel fromChannel
        (λ _ ambient → ambient) (λ _ ambient → ambient) bodyImage₁

    flagsEq :
      (B : Typed.BindGroup) (side : 𝔽 2) →
      proj₂ (Translation.UB[ B ] (physicalEndpoint channel side)
              (SoupTerm.* , physicalEndpoint channel side , SoupTerm.*)) ≡
      proj₂ (Translation.UB[ B ] (physicalEndpoint channel′ side)
              (SoupTerm.* , physicalEndpoint channel′ side , SoupTerm.*))
    flagsEq B side =
      UB-flags-ren B endpointRho (physicalEndpoint channel side)
        (SoupTerm.* , physicalEndpoint channel side , SoupTerm.*)
      ■ sym
          (cong
            (λ endpoint →
              proj₂ (Translation.UB[ B ] endpoint
                      (SoupTerm.* , endpoint , SoupTerm.*)))
            (endpointEq side))

    bindEq : bindChannel B₁ B₂ channel ≡ bindChannel B₁ B₂ channel′
    bindEq =
      cong₂
        (λ flags₁ flags₂ →
          orientChannel (proj₂ channel) (true , flags₁ , flags₂))
        (flagsEq B₁ 0F) (flagsEq B₂ 1F)

    channelContent :
      lookup (Soup.channels C′) (physicalChannel channel′) ≡
      bindChannel B₁ B₂ channel′
    channelContent =
      AmbientEmbedding.ambient-channel-content emb
        (physicalChannel channel) (inj₂ refl)
      ■ channelEq₀ ■ bindEq

    notAmbient : ¬ Transport channelRho ambientChannel (physicalChannel channel′)
    notAmbient (source , ambient , sourceEq) =
      notAmbient₀
        (subst ambientChannel
          (AmbientEmbedding.channelEmbedding-injective emb sourceEq) ambient)

-- Focusing preserves the physical slot assigned to each process thread.
focusImage-thread :
  ∀ {k n c m : ℕ}
  (ctx : ProcessContext k n)
  (P : Typed.Proc k)
  {logicalChannels :
    Vec (OrientedChannel c) (Translation.channelCount (plug ctx P))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set}
  {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m}
  (image : LocalImage (plug ctx P) logicalChannels sigma
    ambientChannel ambientThread C)
  (i : 𝔽 (Translation.processCount P)) →
  threadEmbedding (focused-image (focusImage ctx P image)) i ≡
  threadEmbedding image (threadInContext ctx P i)
focusImage-thread hole P image i = refl
focusImage-thread (par-left ctx Q) P image i =
  focusImage-thread ctx P (par-split-left image) i
focusImage-thread (par-right Q ctx) P image i =
  focusImage-thread ctx P (par-split-right image) i
focusImage-thread (bind B₁ B₂ ctx) P
  {logicalChannels = channel ∷ logicalChannels} image i =
  focusImage-thread ctx P (res-split-image image) i

------------------------------------------------------------------------
-- Separation follows the same descent as the image.  The focused ambient
-- predicates are projections of `focusImage`, so this theorem can be passed
-- directly to the leaves that perform a global phi sweep.

focusSeparated :
  ∀ {k n c m : ℕ}
  (ctx : ProcessContext k n)
  (P : Typed.Proc k)
  {logicalChannels :
    Vec (OrientedChannel c) (Translation.channelCount (plug ctx P))}
  {sigma : Translation.Env n (2 *ℕ c)}
  {ambientChannel : 𝔽 c → Set}
  {ambientThread : 𝔽 m → Set}
  {C : Soup.Config c m} →
  (separated : Separated sigma ambientChannel ambientThread C) →
  (image : LocalImage (plug ctx P) logicalChannels sigma
    ambientChannel ambientThread C) →
  Separated
    (focusEnv ctx P logicalChannels sigma)
    (focusedAmbientChannel (focusImage ctx P image))
    (focusedAmbientThread (focusImage ctx P image)) C
focusSeparated hole P separated image = separated
focusSeparated (par-left ctx Q) P separated image =
  focusSeparated ctx P (separated-par-left separated image)
    (par-split-left image)
focusSeparated (par-right Q ctx) P separated image =
  focusSeparated ctx P (separated-par-right separated image)
    (par-split-right image)
focusSeparated (bind B₁ B₂ ctx) P
  {logicalChannels = channel ∷ logicalChannels} separated image =
  focusSeparated ctx P
    (separated-bind {B₁ = B₁} {B₂ = B₂} separated)
    (res-split-image image)

------------------------------------------------------------------------
-- Close an exact step after it has been lifted to the top level.  Empty
-- source ambients remain logically empty after transport, and the renamed
-- empty environment is pointwise equal to the empty environment.

closeConfigStep :
  {P′ : Typed.Proc 0} {n m n′ m′ : ℕ}
  {C : Soup.Config n m} {C′ : Soup.Config n′ m′} →
  ConfigStep P′ (λ ()) (λ _ → ⊥) (λ _ → ⊥) C C′ →
  GlobalImage P′ C′
closeConfigStep step = record
  { logicalChannels = ConfigStep.config-logicalChannels′ step
  ; localImage =
      ambient-resp
        (λ _ transported → proj₁ (proj₂ transported))
        (λ _ → ⊥-elim)
        (λ _ transported → proj₁ (proj₂ transported))
        (λ _ → ⊥-elim)
        (env-resp (λ ()) (ConfigStep.config-image′ step))
  }
