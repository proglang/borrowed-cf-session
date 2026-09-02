-- | Phase 2 of the forward simulation Typed → UntypedSoup: the local
--   simulation skeleton (`ForwardSoup/PLAN.md`, §3 and §6.2).
--
--   `LocalStep` and the shared leaf infrastructure live in `Local/Step.agda`;
--   this module is the dispatcher over the fourteen typed reduction rules.
--   The three frame rules (`R-Par`, `R-Bind`, `R-Struct`) are proved here from
--   the Phase 1 frame algebra, the leaf rules are discharged by the per-rule
--   modules of Phase 3.
module BorrowedCF.Simulation.ForwardSoup.Local where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)

open import Data.Vec.Relation.Unary.All as AllV using (All)
import Data.Vec.Relation.Unary.All.Properties as AllVP

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.Typed as TypedReduction
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Reduction.Base using (ChanCx)
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)
open Typed using (_;_⊢ₚ_)
open Typed using (inv-∥; inv-ν; bindCtx⇒chanCtx)

open import BorrowedCF.Simulation.ForwardSoup.Expressions using (ValueEnv)
open import BorrowedCF.Simulation.ForwardSoup.Translation using (++ₛ-Value; UB-Value)

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.PhysicalRenaming
  using ( renameEnv; renameOriented; physicalEndpoint-rename
        ; UB-flags-ren; UB-ren-coherent-*; ++ₛ-ren-coherent
        )
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (Separated; env-separated; thread-separated)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.SeparationFrame
  using (separated-bind; separated-par-left)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left; par-split-right; par-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel; res-split-not-ambient; res-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Embedding
  using (ambient-transport; embedChannels; embedThreads; physicalChannel-embed)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Struct using (≋-image)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; GlobalStepImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.ForwardSoup.World.Embedding
  using (Transport; AmbientEmbedding; targetAmbientChannel; targetAmbientThread)

open import BorrowedCF.Simulation.ForwardSoup.Local.Step public
open import BorrowedCF.Simulation.ForwardSoup.Local.Close using (U-close-local)
open import BorrowedCF.Simulation.ForwardSoup.Local.Exp using (U-exp-local)

-- `LocalStep` has fields called `n′`/`m′`, so the homonymous generalisable
-- variables must stay out of scope here.
open Nat.Variables hiding (n′; m′)
open Fin.Patterns

private
  variable a b : ℕ

  -- Inverting `Data.Maybe.map`; the copy in `LocalImage/Embedding.agda` is
  -- private to that module.
  mapMaybe-just :
    (threadRho : 𝔽 a → 𝔽 b) (slot : Maybe (𝔽 a)) {l : 𝔽 b} →
    mapMaybe threadRho slot ≡ just l →
    Σ[ source ∈ 𝔽 a ] (slot ≡ just source × threadRho source ≡ l)
  mapMaybe-just threadRho (just source) refl = source , refl , refl
  mapMaybe-just threadRho nothing ()

  -- The channel-context of a binder-extended scope.
  chanCx-⸴* :
    {Γ₁ : Context.Ctx a} {Γ₂ : Context.Ctx b} →
    ChanCx Γ₁ → ChanCx Γ₂ → ChanCx (Γ₁ Context.⸴* Γ₂)
  chanCx-⸴* = AllVP.++⁺

------------------------------------------------------------------------
-- The local simulation statement.

Local-Sim : Set₁
Local-Sim =
  ∀ {k : ℕ} {Γ : Context.Ctx k} {g : Context.Struct k}
    {P P′ : Typed.Proc k} {n m : ℕ}
    {lc : Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env k (2 *ℕ n)}
    {aC : 𝔽 n → Set} {aT : 𝔽 m → Set}
    {C : Soup.Config n m} →
  ChanCx Γ →
  Γ ; g ⊢ₚ P →
  ValueEnv sigma →
  Separated sigma aC aT C →
  LocalImage P lc sigma aC aT C →
  P TypedReduction.─→ₚ P′ →
  LocalStep P′ sigma aC aT C

------------------------------------------------------------------------
-- The dispatcher.

local-sim : Local-Sim

-- Leaf rules (Phase 3).
local-sim Γ-S ⊢P Vsigma separated image (TypedReduction.R-Exp red) =
  U-exp-local Vsigma image red
local-sim Γ-S ⊢P Vsigma separated image (TypedReduction.R-Fork E V) = {! !}
local-sim Γ-S ⊢P Vsigma separated image (TypedReduction.R-New E) = {! !}
local-sim Γ-S ⊢P Vsigma separated image (TypedReduction.R-Com V) = {! !}
local-sim Γ-S ⊢P Vsigma separated image (TypedReduction.R-Choice E₁ E₂ i) = {! !}
local-sim Γ-S ⊢P Vsigma separated image TypedReduction.R-LSplit = {! !}
local-sim Γ-S ⊢P Vsigma separated image TypedReduction.R-RSplit = {! !}
local-sim Γ-S ⊢P Vsigma separated image TypedReduction.R-Drop = {! !}
local-sim Γ-S ⊢P Vsigma separated image TypedReduction.R-Acq = {! !}
local-sim Γ-S ⊢P Vsigma separated image
  (TypedReduction.R-Close {E₁ = E₁} {E₂ = E₂}) =
  U-close-local {E₁ = E₁} {E₂ = E₂} Vsigma image
local-sim Γ-S ⊢P Vsigma separated image TypedReduction.R-Discard = {! !}

------------------------------------------------------------------------
-- R-Par: split the frame, step on the left, transport the right half along
-- the resulting embedding, join.

local-sim {lc = lc} {sigma = sigma} {aC = aC} {aT = aT} {C = C}
  Γ-S ⊢P Vsigma separated image
  (TypedReduction.R-Par {P = P₀} {Q = Q₀} red)
  with inv-∥ ⊢P
... | _ , _ , _ , ⊢left , _ = record
  { n′ = LocalStep.n′ st
  ; m′ = LocalStep.m′ st
  ; C′ = LocalStep.C′ st
  ; step = LocalStep.step st
  ; embedding = embedding-mono (λ _ → inj₁) (λ _ → inj₁) emb
  ; logicalChannels′ =
      LocalStep.logicalChannels′ st V.++ embedChannels emb rightChannels
  ; image′ =
      par-join (LocalStep.image′ st) rightImage
        right-channels-ambient right-threads-ambient
        ambient-channel-left ambient-channel-right
        ambient-thread-left ambient-thread-right
        ambient-channel-split ambient-thread-split
  }
  where
  channelCountP : ℕ
  channelCountP = Translation.channelCount P₀

  processCountP : ℕ
  processCountP = Translation.processCount P₀

  leftChannels : Vec (OrientedChannel _) channelCountP
  leftChannels = V.take channelCountP lc

  rightChannels : Vec (OrientedChannel _) (Translation.channelCount Q₀)
  rightChannels = V.drop channelCountP lc

  imageLeft = par-split-left image
  imageRight = par-split-right image

  st = local-sim Γ-S ⊢left Vsigma
         (separated-par-left separated image) imageLeft red

  emb = LocalStep.embedding st
  channelRho = AmbientEmbedding.channelEmbedding emb
  threadRho = AmbientEmbedding.threadEmbedding emb

  rightImage =
    ambient-transport emb imageRight
      (λ j → inj₂ (j , refl))
      (λ {j} {l} slotEq → inj₂ (j , slotEq))

  right-channels-ambient :
    (j : 𝔽 (Translation.channelCount Q₀)) →
    Transport channelRho (aC ∪ᵖ ownedChannels rightChannels)
      (physicalChannel (lookup (embedChannels emb rightChannels) j))
  right-channels-ambient j =
    physicalChannel (lookup rightChannels j)
    , inj₂ (j , refl)
    , sym (physicalChannel-embed channelRho rightChannels j)

  right-threads-ambient :
    ∀ {j l} → embedThreads emb imageRight j ≡ just l →
    Transport threadRho
      (aT ∪ᵖ ownedThreads (threadEmbedding image ∘ (processCountP ↑ʳ_))) l
  right-threads-ambient {j} slotEq
    with mapMaybe-just threadRho (threadEmbedding imageRight j) slotEq
  ... | source , sourceEq , threadEq = source , inj₂ (j , sourceEq) , threadEq

  ambient-channel-left :
    (i : 𝔽 (LocalStep.n′ st)) →
    Transport channelRho aC i →
    Transport channelRho (aC ∪ᵖ ownedChannels rightChannels) i
  ambient-channel-left i (source , ambient , sourceEq) =
    source , inj₁ ambient , sourceEq

  ambient-channel-right :
    (i : 𝔽 (LocalStep.n′ st)) →
    Transport channelRho aC i →
    ¬ ownedChannels (embedChannels emb rightChannels) i
  ambient-channel-right i (source , ambient , sourceEq) (j , ownedEq) =
    channel-not-ambient imageRight j
      (inj₁
        (subst aC
          (sym
            (AmbientEmbedding.channelEmbedding-injective emb
              (sym (physicalChannel-embed channelRho rightChannels j)
               ■ ownedEq ■ sym sourceEq)))
          ambient))

  ambient-thread-left :
    (l : 𝔽 (LocalStep.m′ st)) →
    Transport threadRho aT l →
    Transport threadRho
      (aT ∪ᵖ ownedThreads (threadEmbedding image ∘ (processCountP ↑ʳ_))) l
  ambient-thread-left l (source , ambient , sourceEq) =
    source , inj₁ ambient , sourceEq

  ambient-thread-right :
    (l : 𝔽 (LocalStep.m′ st)) →
    Transport threadRho aT l →
    ¬ ownedThreads (embedThreads emb imageRight) l
  ambient-thread-right l (source , ambient , sourceEq) (j , ownedEq)
    with mapMaybe-just threadRho (threadEmbedding imageRight j) ownedEq
  ... | source′ , sourceEq′ , threadEq =
    thread-not-ambient imageRight sourceEq′
      (inj₁
        (subst aT
          (sym
            (AmbientEmbedding.threadEmbedding-injective emb
              (threadEq ■ sym sourceEq)))
          ambient))

  ambient-channel-split :
    (i : 𝔽 (LocalStep.n′ st)) →
    Transport channelRho (aC ∪ᵖ ownedChannels rightChannels) i →
    Transport channelRho aC i ⊎
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
    (l : 𝔽 (LocalStep.m′ st)) →
    Transport threadRho
      (aT ∪ᵖ ownedThreads (threadEmbedding image ∘ (processCountP ↑ʳ_))) l →
    Transport threadRho aT l ⊎ ownedThreads (embedThreads emb imageRight) l
  ambient-thread-split l (source , inj₁ ambient , sourceEq) =
    inj₁ (source , ambient , sourceEq)
  ambient-thread-split l (source , inj₂ (j , ownedEq) , sourceEq) =
    inj₂ (j , (cong (mapMaybe threadRho) ownedEq ■ cong just sourceEq))

------------------------------------------------------------------------
-- R-Bind: hand the bound channel to the frame, step under the binder, and
-- rebuild the restriction over the renamed channel.

local-sim {lc = channel ∷ bodyChannels} {sigma = sigma}
  {aC = aC} {aT = aT} {C = C}
  Γ-S ⊢P Vsigma separated image
  (TypedReduction.R-Bind {B₁ = B₁} {B₂ = B₂} red)
  with inv-ν ⊢P
... | _ , _ , _ , _ , _ , _ , _ , Cx , Cx′ , ⊢body = record
  { n′ = LocalStep.n′ st
  ; m′ = LocalStep.m′ st
  ; C′ = LocalStep.C′ st
  ; step = LocalStep.step st
  ; embedding = embedding-mono (λ _ → inj₁) (λ _ ambient → ambient) emb
  ; logicalChannels′ = channel′ ∷ LocalStep.logicalChannels′ st
  ; image′ = res-join bodyImage₂ channelContent notAmbient
  }
  where
  Γ-S′ = chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx Cx) (bindCtx⇒chanCtx Cx′)) Γ-S

  bodyImage₀ = res-split-image image
  channelEq₀ = res-split-channel image
  notAmbient₀ = res-split-not-ambient image

  Vsigma′ : ValueEnv (bindEnv B₁ B₂ channel sigma)
  Vsigma′ =
    ++ₛ-Value
      (++ₛ-Value
        (UB-Value B₁ (physicalEndpoint channel 0F)
          SoupExpression.V-K SoupExpression.V-K)
        (UB-Value B₂ (physicalEndpoint channel 1F)
          SoupExpression.V-K SoupExpression.V-K))
      Vsigma

  separated′ :
    Separated (bindEnv B₁ B₂ channel sigma)
      (aC ∪ᵖ singletonᵖ (physicalChannel channel)) aT C
  separated′ =
    separated-bind {B₁ = B₁} {B₂ = B₂} {channel = channel} separated

  st = local-sim Γ-S′ ⊢body Vsigma′ separated′ bodyImage₀ red

  emb = LocalStep.embedding st
  channelRho = AmbientEmbedding.channelEmbedding emb
  endpointRho = AmbientEmbedding.endpointEmbedding emb

  channel′ : OrientedChannel (LocalStep.n′ st)
  channel′ = renameOriented channelRho channel

  endpointEq :
    (side : 𝔽 2) →
    physicalEndpoint channel′ side ≡ endpointRho (physicalEndpoint channel side)
  endpointEq =
    physicalEndpoint-rename channelRho endpointRho
      (AmbientEmbedding.endpoint-respects-channel emb) channel

  -- The binder environment of the renamed channel is the renaming of the
  -- binder environment of the original one.
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

  bodyImage₁ = env-resp envEq (LocalStep.image′ st)

  toChannel :
    (i : 𝔽 (LocalStep.n′ st)) →
    Transport channelRho (aC ∪ᵖ singletonᵖ (physicalChannel channel)) i →
    (Transport channelRho aC ∪ᵖ singletonᵖ (physicalChannel channel′)) i
  toChannel i (source , inj₁ ambient , sourceEq) =
    inj₁ (source , ambient , sourceEq)
  toChannel i (source , inj₂ headEq , sourceEq) =
    inj₂ (cong channelRho headEq ■ sourceEq)

  fromChannel :
    (i : 𝔽 (LocalStep.n′ st)) →
    (Transport channelRho aC ∪ᵖ singletonᵖ (physicalChannel channel′)) i →
    Transport channelRho (aC ∪ᵖ singletonᵖ (physicalChannel channel)) i
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
    lookup (Soup.channels (LocalStep.C′ st)) (physicalChannel channel′) ≡
    bindChannel B₁ B₂ channel′
  channelContent =
    AmbientEmbedding.ambient-channel-content emb
      (physicalChannel channel) (inj₂ refl)
    ■ channelEq₀ ■ bindEq

  notAmbient : ¬ Transport channelRho aC (physicalChannel channel′)
  notAmbient (source , ambient , sourceEq) =
    notAmbient₀
      (subst aC
        (AmbientEmbedding.channelEmbedding-injective emb sourceEq) ambient)

------------------------------------------------------------------------
-- R-Struct: move the image across the two congruences.

local-sim Γ-S ⊢P Vsigma separated image
  (TypedReduction.R-Struct eq₁ red eq₂) = record
  { n′ = LocalStep.n′ st
  ; m′ = LocalStep.m′ st
  ; C′ = LocalStep.C′ st
  ; step = LocalStep.step st
  ; embedding = LocalStep.embedding st
  ; logicalChannels′ = proj₁ target
  ; image′ = proj₂ target
  }
  where
  source = ≋-image eq₁ image
  st = local-sim Γ-S (Γ-S / ⊢P ⊢-≋ eq₁) Vsigma separated (proj₂ source) red
  target = ≋-image eq₂ (LocalStep.image′ st)

------------------------------------------------------------------------
-- The closed instance.

sim-global :
  {P P′ : Typed.Proc 0} {n m : ℕ} {C : Soup.Config n m} →
  [] ; Context.[] ⊢ₚ P →
  GlobalImage P C →
  P TypedReduction.─→ₚ P′ →
  GlobalStepImage P′ C
sim-global {C = C} ⊢P image red =
  _ , _ , LocalStep.C′ st , LocalStep.step st
  , record
      { logicalChannels = LocalStep.logicalChannels′ st
      ; localImage =
          ambient-resp
            (λ _ transported → proj₁ (proj₂ transported))
            (λ _ → ⊥-elim)
            (λ _ transported → proj₁ (proj₂ transported))
            (λ _ → ⊥-elim)
            (env-resp (λ ()) (LocalStep.image′ st))
      }
  where
  separated : Separated {k = 0} (λ ()) (λ _ → ⊥) (λ _ → ⊥) C
  separated = record { env-separated = λ () ; thread-separated = λ _ () }

  st = local-sim AllV.[] ⊢P (λ ()) separated (localImage image) red
